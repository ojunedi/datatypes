//! The middle "end" of our compiler is the part that transforms our well-formed
//! source-language abstract syntax tree (AST) into the intermediate representation

use crate::ast::{self, *};
use crate::ssa::{self, *};
use crate::{frontend::Resolver, identifiers::*};
use std::collections::{HashMap, HashSet};

pub struct Lowerer {
    pub vars: IdGen<VarName>,
    pub funs: IdGen<FunName>,
    pub blocks: IdGen<BlockName>,
    /// The live variables at the start of each function.
    fun_scopes: HashMap<FunName, Vec<VarName>>,
    /// The functions that should be lambda lifted.
    should_lift: HashSet<FunName>,
    /// The name of the basic block generated for each function.
    fun_as_block: HashMap<FunName, BlockName>,
    /// Lifted functions. Removed after the lowering pass.
    lifted_funs: Vec<(FunBlock, BasicBlock)>,
}

/// A helper struct for variable renaming.
#[derive(Clone)]
struct Substitution {
    /// The map of old variables to new variables.
    rename_map: HashMap<VarName, VarName>,
}
impl Substitution {
    fn new() -> Self {
        Substitution {
            rename_map: HashMap::new(),
        }
    }
    fn insert(&mut self, old: VarName, new: VarName) {
        self.rename_map.insert(old, new);
    }
    fn run(&self, mut var: VarName) -> VarName {
        while let Some(new) = self.rename_map.get(&var) {
            var = new.to_owned();
        }
        var
    }
}

/// Indicates whether the expression being compiled is in a tail position.
#[derive(Clone, Debug)]
enum Continuation {
    Return,
    Block(VarName, BlockBody),
}

impl Continuation {
    fn invoke(self, imm: Immediate) -> BlockBody {
        match self {
            Continuation::Return => BlockBody::Terminator(Terminator::Return(imm)),
            Continuation::Block(dest, b) => BlockBody::Operation {
                dest,
                op: Operation::Immediate(imm),
                next: Box::new(b),
            },
        }
    }
}

impl From<Resolver> for Lowerer {
    fn from(resolver: Resolver) -> Self {
        let Resolver { vars, funs, .. } = resolver;
        Lowerer {
            vars,
            funs,
            blocks: IdGen::new(),
            fun_scopes: HashMap::new(),
            should_lift: HashSet::new(),
            fun_as_block: HashMap::new(),
            lifted_funs: Vec::new(),
        }
    }
}

/// Traverse the AST and collect the live variables at the start of each function.
/// Also collect the functions that are non-tail called and the functions that are called
/// by a lifted function, either tail or non-tail.
struct Lifter {
    /// Functions that are non-tail called.
    non_tail_called_funs: HashSet<FunName>,
    /// The call graph of the program.
    /// Records all functions that are called, either tail or non-tail.
    /// Used to lift all functions called by a lifted function.
    fun_calls: HashMap<FunName, HashSet<FunName>>,
}

impl Lifter {
    /// What should be lambda lifted?
    /// 1. Any function that is called with a non-tail call.
    /// 2. Any function that is called by a lifted function.
    pub fn should_lift(&self) -> HashSet<FunName> {
        let mut should_lift = HashSet::new();
        // find all functions that should be lifted
        let mut worklist = self
            .non_tail_called_funs
            .iter()
            .cloned()
            .collect::<Vec<_>>();
        while let Some(fun) = worklist.pop() {
            // 1. include the function in worklist to the result set
            if should_lift.insert(fun.clone()) {
                // 2. if it's the first time met, add all functions that it calls to the worklist
                worklist.extend(self.fun_calls.get(&fun).cloned().unwrap_or_default());
            }
        }
        should_lift
    }
}

impl Lifter {
    fn new() -> Self {
        Self {
            non_tail_called_funs: HashSet::new(),
            fun_calls: HashMap::new(),
        }
    }

    fn lift_prog(&mut self, prog: &BoundProg) {
        let Prog {externs: _, name, param: _, body, loc: _,} = prog;
        self.lift_expr(body, &name, true);
    }

    fn lift_expr(&mut self, e: &BoundExpr, site: &FunName, tail_position: bool) {
        match e {
            Expr::Num(_, _) | Expr::Bool(_, _) | Expr::Var(_, _) => {}
            Expr::Prim {prim: _, args, loc: _,} => {
                for arg in args {
                    self.lift_expr(arg, site, false);
                }
            }
            Expr::Let {bindings, body, loc: _,} => {
                for Binding { var: _, expr } in bindings {
                    self.lift_expr(expr, site, false);
                }
                self.lift_expr(body, site, tail_position);
            }
            Expr::If {cond, thn, els, loc: _,} => {
                self.lift_expr(cond, site, false);
                self.lift_expr(thn, site, tail_position);
                self.lift_expr(els, site, tail_position);
            }
            Expr::FunDefs {decls, body, loc: _,} => {
                for FunDecl { name, body, .. } in decls {
                    self.lift_expr(body, name, true);
                }
                self.lift_expr(body, site, tail_position);
            }
            Expr::Call { fun, args, loc: _ } => {
                if !tail_position {
                    self.non_tail_called_funs.insert(fun.clone());
                }
                self.fun_calls
                    .entry(site.clone())
                    .or_default()
                    .insert(fun.clone());
                for arg in args {
                    self.lift_expr(arg, site, false);
                }
            }
        }
    }
}

impl Lowerer {
    pub fn lower_prog(&mut self, prog: BoundProg) -> Program {
        // first, collect all functions that should be lifted
        let mut lifter = Lifter::new();
        lifter.lift_prog(&prog);
        self.should_lift = lifter.should_lift();

        // then, lower the program
        let Prog {externs, name, param, body, loc: _,} = prog;
        // register function scope for the main function
        self.fun_scopes.insert(name.clone(), Vec::new());
        // create a block name for the main function
        let block = self.blocks.fresh(name.hint());
        self.fun_as_block.insert(name.clone(), block.clone());
        // lower the externs
        let externs = Vec::from_iter(externs.into_iter().map(
            |ExtDecl {name, params, loc: _,}| Extern {
                name,
                params: params.into_iter().map(|(p, _)| p).collect(),
            },
        ));
        // lower the parameter
        let (param, _) = param;
        // lower the body
        let body = self.lower_expr_kont(body, &vec![param.clone()], &Substitution::new(), Continuation::Return,);
        // collect the lifted functions and blocks
        let (mut funs, mut blocks): (Vec<FunBlock>, Vec<BasicBlock>) =
            std::mem::take(&mut self.lifted_funs).into_iter().unzip();
        // create the entry block and function
        blocks.push(BasicBlock {
            label: block.clone(),
            params: vec![param.clone()],
            body,
        });
        let fun_param = self.vars.fresh(param.hint());
        funs.push(FunBlock {
            name,
            params: vec![fun_param.clone()],
            body: Branch {
                target: block,
                args: vec![Immediate::Var(fun_param)],
            },
        });
        Program {externs, funs, blocks,}
    }

    fn kont_to_block(&mut self, k: Continuation) -> (VarName, BlockBody) {
        match k {
            Continuation::Block(x, b) => (x, b),
            Continuation::Return => {
                let x = self.vars.fresh("result");
                (
                    x.clone(),
                    BlockBody::Terminator(Terminator::Return(Immediate::Var(x))),
                )
            }
        }
    }

    /// Compiles an expression to a basic block that uses the continuation k on
    /// the value e produces.
    fn lower_expr_kont(&mut self, e: BoundExpr, live: &[VarName], subst: &Substitution, k: Continuation) -> BlockBody {
        match e {
            Expr::Num(n, _) => k.invoke(Immediate::Const(n << 1)),
            Expr::Bool(b, _) => k.invoke(if b {
                Immediate::Const(0b101 as i64)
            } else {
                Immediate::Const(0b001)
            }),
            Expr::Var(v, _) => k.invoke(Immediate::Var(subst.run(v))),
            Expr::Prim { prim, args, loc: _ } => {
                let lower_unary =
                    |lowerer: &mut Lowerer,
                     assert_ty: Type,
                     args: Vec<BoundExpr>,
                     k: Continuation,
                     make_op: fn(Immediate) -> Operation| {
                        let arg = args.into_iter().next().unwrap();
                        let arg_var = lowerer.vars.fresh("unary_arg");
                        let (dest, next) = lowerer.kont_to_block(k);

                        let body = BlockBody::AssertType {
                            ty: assert_ty,
                            arg: Immediate::Var(arg_var.clone()),
                            next: Box::new(BlockBody::Operation {
                                dest,
                                op: make_op(Immediate::Var(arg_var.clone())),
                                next: Box::new(next),
                            }),
                        };

                        lowerer.lower_expr_kont(arg, live, subst, Continuation::Block(arg_var, body),)
                    };
                let lower_binary =
                    |lowerer: &mut Lowerer,
                     assert_ty: Type,
                     args: Vec<BoundExpr>,
                     k: Continuation,
                     make_op: fn(Immediate, Immediate) -> Operation| {
                        let mut args = args.into_iter();
                        let lhs = args.next().unwrap();
                        let rhs = args.next().unwrap();
                        let lhs_var = lowerer.vars.fresh("bin_lhs");
                        let rhs_var = lowerer.vars.fresh("bin_rhs");
                        let (dest, next) = lowerer.kont_to_block(k);

                        let body = BlockBody::AssertType {
                            ty: assert_ty,
                            arg: Immediate::Var(lhs_var.clone()),
                            next: Box::new(BlockBody::AssertType {
                                ty: assert_ty,
                                arg: Immediate::Var(rhs_var.clone()),
                                next: Box::new(BlockBody::Operation {
                                    dest,
                                    op: make_op(
                                        Immediate::Var(lhs_var.clone()),
                                        Immediate::Var(rhs_var.clone()),
                                    ),
                                    next: Box::new(next),
                                }),
                            }),
                        };

                        let body = lowerer.lower_expr_kont(rhs, live, subst, Continuation::Block(rhs_var, body),);
                        lowerer.lower_expr_kont(lhs, live, subst, Continuation::Block(lhs_var, body),)
                    };
                let lower_cmp = |lowerer: &mut Lowerer,
                                 prim2: Prim2,
                                 args: Vec<BoundExpr>,
                                 k: Continuation,
                                 assert_ty: Type| {
                    let mut args = args.into_iter();
                    let lhs = args.next().unwrap();
                    let rhs = args.next().unwrap();
                    let lhs_var = lowerer.vars.fresh("cmp_lhs");
                    let rhs_var = lowerer.vars.fresh("cmp_rhs");
                    let cmp_var = lowerer.vars.fresh("cmp_result");
                    let shifted = lowerer.vars.fresh("cmp_shifted");
                    let (dest, next) = lowerer.kont_to_block(k);

                    let tag_bool = BlockBody::Operation {
                        dest: cmp_var.clone(),
                        op: Operation::Prim2(
                            prim2,
                            Immediate::Var(lhs_var.clone()),
                            Immediate::Var(rhs_var.clone()),
                        ),
                        next: Box::new(BlockBody::Operation {
                            dest: shifted.clone(),
                            op: Operation::Prim1(Prim1::BitSal(2), Immediate::Var(cmp_var.clone())),
                            next: Box::new(BlockBody::Operation {
                                dest,
                                op: Operation::Prim2(
                                    Prim2::BitOr,
                                    Immediate::Var(shifted.clone()),
                                    Immediate::Const(0b001),
                                ),
                                next: Box::new(next),
                            }),
                        }),
                    };

                    let body = BlockBody::AssertType {
                        ty: assert_ty,
                        arg: Immediate::Var(lhs_var.clone()),
                        next: Box::new(BlockBody::AssertType {
                            ty: assert_ty,
                            arg: Immediate::Var(rhs_var.clone()),
                            next: Box::new(tag_bool),
                        }),
                    };

                    let body = lowerer.lower_expr_kont(rhs, live, subst, Continuation::Block(rhs_var, body),);
                    lowerer.lower_expr_kont(lhs, live, subst, Continuation::Block(lhs_var, body))
                };
                match prim {
                    Prim::Add1 => lower_unary(self, Type::Int, args, k, |a| Operation::Prim2(Prim2::Add, a, Immediate::Const(2))),
                    Prim::Sub1 => lower_unary(self, Type::Int, args, k, |a| Operation::Prim2(Prim2::Sub, a, Immediate::Const(2))),
                    Prim::Not => lower_unary(self, Type::Bool, args, k, |a| Operation::Prim2(Prim2::BitXor, a, Immediate::Const(0b100))),
                    Prim::Add => lower_binary(self, Type::Int, args, k, |a, b| Operation::Prim2(Prim2::Add, a, b)),
                    Prim::Sub => lower_binary(self, Type::Int, args, k, |a, b| Operation::Prim2(Prim2::Sub, a, b)),
                    Prim::And => lower_binary(self, Type::Bool, args, k, |a, b| Operation::Prim2(Prim2::BitAnd, a, b)),
                    Prim::Or => lower_binary(self, Type::Bool, args, k, |a, b| Operation::Prim2(Prim2::BitOr, a, b)),
                    Prim::Lt => lower_cmp(self, Prim2::Lt, args, k, Type::Int),
                    Prim::Le => lower_cmp(self, Prim2::Le, args, k, Type::Int),
                    Prim::Gt => lower_cmp(self, Prim2::Gt, args, k, Type::Int),
                    Prim::Ge => lower_cmp(self, Prim2::Ge, args, k, Type::Int),
                    Prim::Mul => {
                        // need to untag one of the arguments before we multiply them
                        // 2n * 2m = 4mn
                        // n * 2m = 2mn
                        let mut args = args.into_iter();
                        let lhs = args.next().unwrap();
                        let rhs = args.next().unwrap();
                        let lhs_var = self.vars.fresh("sub_lhs");
                        let rhs_var = self.vars.fresh("sub_rhs");
                        let untagged = self.vars.fresh("untagged");
                        let (dest, next) = self.kont_to_block(k);
                        let body = BlockBody::AssertType {
                            ty: Type::Int,
                            arg: Immediate::Var(lhs_var.clone()),
                            next: Box::new(BlockBody::Operation {
                                dest: untagged.clone(),
                                op: Operation::Prim1(
                                    Prim1::BitSar(1),
                                    Immediate::Var(lhs_var.clone()),
                                ),
                                next: Box::new(BlockBody::AssertType {
                                    ty: Type::Int,
                                    arg: Immediate::Var(rhs_var.clone()),
                                    next: Box::new(BlockBody::Operation {
                                        dest,
                                        op: Operation::Prim2(
                                            Prim2::Mul,
                                            Immediate::Var(untagged.clone()),
                                            Immediate::Var(rhs_var.clone()),
                                        ),
                                        next: Box::new(next),
                                    }),
                                }),
                            }),
                        };
                        let body = self.lower_expr_kont(rhs, live, subst, Continuation::Block(rhs_var, body),);
                        self.lower_expr_kont(lhs, live, subst, Continuation::Block(lhs_var, body))
                    }
                    Prim::Eq => {
                        let mut arg = args.into_iter();
                        let lhs = arg.next().unwrap();
                        let rhs = arg.next().unwrap();

                        let lhs_var = self.vars.fresh("eq_lhs");
                        let rhs_var = self.vars.fresh("eq_rhs");
                        let shifted = self.vars.fresh("shifted");
                        let cmp_var = self.vars.fresh("cmp_var");
                        let (dest, next) = self.kont_to_block(k);

                        // don't have to assert types because we just compare our internal
                        // representation (tagged values) to compare types as well
                        let body = BlockBody::Operation {
                            dest: cmp_var.clone(),
                            op: Operation::Prim2(
                                Prim2::Eq,
                                Immediate::Var(lhs_var.clone()),
                                Immediate::Var(rhs_var.clone()),
                            ),
                            next: Box::new(BlockBody::Operation {
                                dest: shifted.clone(),
                                op: Operation::Prim1(
                                    Prim1::BitSal(2),
                                    Immediate::Var(cmp_var.clone()),
                                ),
                                next: Box::new(BlockBody::Operation {
                                    dest,
                                    op: Operation::Prim2(
                                        Prim2::BitOr,
                                        Immediate::Var(shifted.clone()),
                                        Immediate::Const(0b001),
                                    ),
                                    next: Box::new(next),
                                }),
                            }),
                        };
                        let body = self.lower_expr_kont(rhs, live, subst, Continuation::Block(rhs_var, body),);
                        self.lower_expr_kont(lhs, live, subst, Continuation::Block(lhs_var, body))
                    }
                    Prim::Neq => {
                        let mut arg = args.into_iter();
                        let lhs = arg.next().unwrap();
                        let rhs = arg.next().unwrap();

                        let lhs_var = self.vars.fresh("eq_lhs");
                        let rhs_var = self.vars.fresh("eq_rhs");
                        let shifted = self.vars.fresh("shifted");
                        let cmp_var = self.vars.fresh("cmp_var");
                        let (dest, next) = self.kont_to_block(k);

                        // don't have to assert types because we just compare our internal
                        // representation (tagged values) to compare types as well
                        let body = BlockBody::Operation {
                            dest: cmp_var.clone(),
                            op: Operation::Prim2(
                                Prim2::Neq,
                                Immediate::Var(lhs_var.clone()),
                                Immediate::Var(rhs_var.clone()),
                            ),
                            next: Box::new(BlockBody::Operation {
                                dest: shifted.clone(),
                                op: Operation::Prim1(
                                    Prim1::BitSal(2),
                                    Immediate::Var(cmp_var.clone()),
                                ),
                                next: Box::new(BlockBody::Operation {
                                    dest,
                                    op: Operation::Prim2(
                                        Prim2::BitOr,
                                        Immediate::Var(shifted.clone()),
                                        Immediate::Const(0b001),
                                    ),
                                    next: Box::new(next),
                                }),
                            }),
                        };
                        let body = self.lower_expr_kont(rhs, live, subst, Continuation::Block(rhs_var, body),);
                        self.lower_expr_kont(lhs, live, subst, Continuation::Block(lhs_var, body))
                    },
                    Prim::IsType(ty) => {
                        // is the argument of the given `ty` type
                        // check arg's tag matches ty tag
                        // return a tagged boolean
                        let arg = args.into_iter().next().unwrap();
                        let arg_var = self.vars.fresh("type_var");
                        let masked = self.vars.fresh("masked_var");
                        let cmp_var = self.vars.fresh("cmp_var");
                        let shifted = self.vars.fresh("shifted_var");
                        let (dest, next) = self.kont_to_block(k);

                        let body = BlockBody::Operation {
                            dest: masked.clone(),
                            op: Operation::Prim2(Prim2::BitAnd, Immediate::Var(arg_var.clone()), Immediate::Const(ty.mask())),
                            next: Box::new(BlockBody::Operation {
                                dest: cmp_var.clone(),
                                op: Operation::Prim2(Prim2::Eq, Immediate::Var(masked.clone()), Immediate::Const(ty.tag())),
                                next: Box::new(BlockBody::Operation {
                                    dest: shifted.clone(),
                                    op: Operation::Prim1(Prim1::BitSal(2), Immediate::Var(cmp_var.clone())),
                                    next: Box::new(BlockBody::Operation {
                                        dest,
                                        op: Operation::Prim2(Prim2::BitOr, Immediate::Var(shifted.clone()), Immediate::Const(0b001)),
                                        next: Box::new(next),
                                    }),
                                }),
                            })
                        };
                        self.lower_expr_kont(arg, live, subst, Continuation::Block(arg_var, body))
                    }
                    Prim::NewArray => {
                        let arg = args.into_iter().next().unwrap();
                        let arg_var = self.vars.fresh("arg_var");
                        let untagged = self.vars.fresh("arg_len");
                        let ptr = self.vars.fresh("heap_ptr");
                        let (dest, next) = self.kont_to_block(k);
                        let body = BlockBody::AssertType { // assert N is int
                            ty: Type::Int,
                            arg: Immediate::Var(arg_var.clone()),
                            next: Box::new(BlockBody::Operation {
                                dest: untagged.clone(),
                                op: Operation::Prim1(Prim1::BitSar(1), Immediate::Var(arg_var.clone())), // untag N
                                next: Box::new(BlockBody::AssertLength { // assert N >= 0
                                    len: Immediate::Var(untagged.clone()),
                                    next: Box::new(BlockBody::Operation {
                                        dest: ptr.clone(),
                                        op: Operation::AllocateArray { len: Immediate::Var(untagged.clone())}, // allocate the array
                                        next: Box::new(BlockBody::Operation {
                                            dest,
                                            op: Operation::Prim2(Prim2::BitOr, Immediate::Var(ptr.clone()), Immediate::Const(0b11)), // tag array with 0b11 on the end
                                            next: Box::new(next)
                                        })
                                    })
                                })
                            })
                        };
                        self.lower_expr_kont(arg, live, subst, Continuation::Block(arg_var, body))
                    },
                    Prim::MakeArray => {
                        let len = args.len() as i64;
                        let arg_vars: Vec<VarName> = args.iter().enumerate()
                            .map(|(i, _)| self.vars.fresh(format!("arr_elem_{}", i)))
                            .collect();
                        let ptr = self.vars.fresh("heap_ptr");
                        let (dest, next) = self.kont_to_block(k);

                        // innermost: tag the pointer and continue
                        let mut body = BlockBody::Operation {
                            dest,
                            op: Operation::Prim2(Prim2::BitOr, Immediate::Var(ptr.clone()), Immediate::Const(0b11)),
                            next: Box::new(next),
                        };

                        // stores in reverse: store each element at offset i+1
                        for (i, var) in arg_vars.iter().enumerate().rev() {
                            body = BlockBody::Store {
                                addr: Immediate::Var(ptr.clone()),
                                offset: Immediate::Const((i + 1) as i64),
                                val: Immediate::Var(var.clone()),
                                next: Box::new(body),
                            };
                        }

                        // allocate the array
                        body = BlockBody::Operation {
                            dest: ptr.clone(),
                            op: Operation::AllocateArray { len: Immediate::Const(len) },
                            next: Box::new(body),
                        };

                        // evaluate each arg in reverse
                        for (arg, var) in args.into_iter().zip(arg_vars).rev() {
                            body = self.lower_expr_kont(arg, live, subst, Continuation::Block(var, body));
                        }

                        body
                    }
                    Prim::ArrayGet => {
                        let mut args = args.into_iter();
                        let arr = args.next().unwrap();
                        let ind = args.next().unwrap();
                        let arr_var = self.vars.fresh("arr_var");
                        let ind_var = self.vars.fresh("ind_var");
                        let untagged_idx = self.vars.fresh("untagged_idx");
                        let arr_len = self.vars.fresh("arr_len");
                        let untagged_arr = self.vars.fresh("untagged_arr");
                        let offset_var = self.vars.fresh("arr_offset");
                        let (dest, next) = self.kont_to_block(k);

                        let body = BlockBody::AssertType { // assert arr
                            ty: Type::Array,
                            arg: Immediate::Var(arr_var.clone()),
                            next: Box::new(BlockBody::AssertType { // assert int
                                ty: Type::Int,
                                arg: Immediate::Var(ind_var.clone()),
                                next: Box::new(BlockBody::Operation {
                                    dest: untagged_idx.clone(),
                                    op: Operation::Prim1(Prim1::BitSar(1), Immediate::Var(ind_var.clone())), // untag index
                                    next: Box::new(BlockBody::Operation {
                                        dest: untagged_arr.clone(),
                                        op: Operation::Prim2(Prim2::BitAnd, Immediate::Var(arr_var.clone()), Immediate::Const(!0b11)), // untag arr
                                        next: Box::new(BlockBody::Operation {
                                            dest: arr_len.clone(),
                                            op: Operation::Load { addr: Immediate::Var(untagged_arr.clone()), offset: Immediate::Const(0) },
                                            next: Box::new(BlockBody::AssertInBounds {
                                                bound: Immediate::Var(arr_len.clone()),
                                                arg: Immediate::Var(untagged_idx.clone()),
                                                next: Box::new(BlockBody::Operation {
                                                    dest: offset_var.clone(),
                                                    op: Operation::Prim2(Prim2::Add, Immediate::Var(untagged_idx.clone()), Immediate::Const(1)),
                                                    next: Box::new(BlockBody::Operation {
                                                        dest,
                                                        op: Operation::Load {
                                                            addr: Immediate::Var(untagged_arr.clone()),
                                                            offset: Immediate::Var(offset_var.clone()),
                                                        },
                                                        next: Box::new(next),
                                                    }),
                                                }),
                                            })
                                        })
                                    })
                                })
                            })
                        };

                        let body = self.lower_expr_kont(ind, live, subst, Continuation::Block(ind_var, body));
                        self.lower_expr_kont(arr, live, subst, Continuation::Block(arr_var, body))
                    }
                    Prim::ArraySet => {
                        let mut args = args.into_iter();
                        let arr = args.next().unwrap();
                        let ind = args.next().unwrap();
                        let val = args.next().unwrap();
                        let arr_var = self.vars.fresh("arr_var");
                        let ind_var = self.vars.fresh("ind_var");
                        let val_var = self.vars.fresh("val_var");
                        let untagged_idx = self.vars.fresh("untagged_idx");
                        let arr_len = self.vars.fresh("arr_len");
                        let untagged_arr = self.vars.fresh("untagged_arr");
                        let offset_var = self.vars.fresh("arr_offset");
                        let (dest, next) = self.kont_to_block(k);

                        let body = BlockBody::AssertType { // assert arr
                            ty: Type::Array,
                            arg: Immediate::Var(arr_var.clone()),
                            next: Box::new(BlockBody::AssertType { // assert int
                                ty: Type::Int,
                                arg: Immediate::Var(ind_var.clone()),
                                next: Box::new(BlockBody::Operation {
                                    dest: untagged_idx.clone(),
                                    op: Operation::Prim1(Prim1::BitSar(1), Immediate::Var(ind_var.clone())), // untag index
                                    next: Box::new(BlockBody::Operation {
                                        dest: untagged_arr.clone(),
                                        op: Operation::Prim2(Prim2::BitAnd, Immediate::Var(arr_var.clone()), Immediate::Const(!0b11)), // untag arr
                                        next: Box::new(BlockBody::Operation {
                                            dest: arr_len.clone(),
                                            op: Operation::Load { addr: Immediate::Var(untagged_arr.clone()), offset: Immediate::Const(0) },
                                            next: Box::new(BlockBody::AssertInBounds {
                                                bound: Immediate::Var(arr_len.clone()),
                                                arg: Immediate::Var(untagged_idx.clone()),
                                                next: Box::new(BlockBody::Operation {
                                                    dest: offset_var.clone(),
                                                    op: Operation::Prim2(Prim2::Add, Immediate::Var(untagged_idx.clone()), Immediate::Const(1)),
                                                    next: Box::new(BlockBody::Store {
                                                        addr: Immediate::Var(untagged_arr.clone()),
                                                        offset: Immediate::Var(offset_var.clone()),
                                                        val: Immediate::Var(val_var.clone()),
                                                        next: Box::new(BlockBody::Operation {
                                                            dest,
                                                            op: Operation::Immediate(Immediate::Var(val_var.clone())),
                                                            next: Box::new(next),
                                                        }),
                                                    }),
                                                }),
                                            }),
                                        }),
                                    }),
                                }),
                            }),
                        };

                        let body = self.lower_expr_kont(val, live, subst, Continuation::Block(val_var, body));
                        let body = self.lower_expr_kont(ind, live, subst, Continuation::Block(ind_var, body));
                        self.lower_expr_kont(arr, live, subst, Continuation::Block(arr_var, body))
                    },
                    Prim::Length => {
                        // get arr and check it's an array

                        let arr = args.into_iter().next().unwrap();
                        let arr_var = self.vars.fresh("arg_var");
                        let untagged_arr = self.vars.fresh("untagged_arr");
                        let untagged_len = self.vars.fresh("untagged_len");
                        let (dest, next) = self.kont_to_block(k);


                        let body = BlockBody::AssertType { // assert arr
                            ty: Type::Array,
                            arg: Immediate::Var(arr_var.clone()),
                            next: Box::new(BlockBody::Operation {
                                dest: untagged_arr.clone(),
                                op: Operation::Prim2(Prim2::BitAnd, Immediate::Var(arr_var.clone()), Immediate::Const(!0b11)), // untag arr
                                next: Box::new(BlockBody::Operation {
                                    dest: untagged_len.clone(),
                                    op: Operation::Load { addr: Immediate::Var(untagged_arr.clone()), offset: Immediate::Const(0) },
                                    next: Box::new(BlockBody::Operation {
                                        dest,
                                        op: Operation::Prim1(Prim1::BitSal(1), Immediate::Var(untagged_len.clone())), // tag the int
                                        next: Box::new(next),
                                    })
                                })
                            })
                        };

                        self.lower_expr_kont(arr, live, subst, Continuation::Block(arr_var.clone(), body))

                    },
                }
            }
            Expr::Let {bindings, body, loc: _,} => {
                // collect the live variables up to this point
                let mut live = live
                    .to_owned()
                    .into_iter()
                    .chain(
                        bindings
                            .iter()
                            .map(|Binding { var: (var, _), .. }| var.clone()),
                    )
                    .collect::<Vec<_>>();

                // backwards, here we go
                let block = self.lower_expr_kont(*body, &live, subst, k);

                // reversed, as usual
                bindings.into_iter().rev().fold(
                    block,
                    |block,
                     Binding {var: (var, _), expr}| {
                        live.pop();
                        let expr = self.lower_expr_kont(expr, &live, subst, Continuation::Block(var.clone(), block),);
                        expr
                    },
                )
            }
            Expr::If { cond, thn, els, loc: _, } => {
                let cond_var = self.vars.fresh("cond_var");
                let test_var = self.vars.fresh("cond_test");
                let thn_block = self.blocks.fresh("then");
                let els_block = self.blocks.fresh("else");

                let (thn_cont, els_cont, join_blocks) = match k {
                    Continuation::Return => {
                        (Continuation::Return, Continuation::Return, vec![])
                    }
                    Continuation::Block(dest, next) => {
                        let join_block = self.blocks.fresh("join");
                        let thn_result = self.vars.fresh("thn_result");
                        let thn_cont = Continuation::Block(
                            thn_result.clone(),
                            BlockBody::Terminator(Terminator::Branch(Branch {
                                target: join_block.clone(),
                                args: vec![Immediate::Var(thn_result)],
                            })),
                        );
                        let els_result = self.vars.fresh("els_result");
                        let els_cont = Continuation::Block(
                            els_result.clone(),
                            BlockBody::Terminator(Terminator::Branch(Branch {
                                target: join_block.clone(),
                                args: vec![Immediate::Var(els_result)],
                            })),
                        );
                        let join = BasicBlock {
                            label: join_block,
                            params: vec![dest],
                            body: next,
                        };
                        (thn_cont, els_cont, vec![join])
                    }
                };

                let thn_body = self.lower_expr_kont(*thn, live, subst, thn_cont);
                let els_body = self.lower_expr_kont(*els, live, subst, els_cont);

                let mut blocks = vec![
                    BasicBlock { label: thn_block.clone(), params: vec![], body: thn_body },
                    BasicBlock { label: els_block.clone(), params: vec![], body: els_body },
                ];
                blocks.extend(join_blocks);

                let body = BlockBody::AssertType {
                    ty: Type::Bool,
                    arg: Immediate::Var(cond_var.clone()),
                    next: Box::new(BlockBody::Operation {
                        dest: test_var.clone(),
                        op: Operation::Prim2(Prim2::BitAnd, Immediate::Var(cond_var.clone()), Immediate::Const(0b100)),
                        next: Box::new(BlockBody::SubBlocks {
                            blocks,
                            next: Box::new(BlockBody::Terminator(Terminator::ConditionalBranch {
                                cond: Immediate::Var(test_var.clone()),
                                thn: thn_block,
                                els: els_block,
                            })),
                        }),
                    }),
                };

                self.lower_expr_kont(*cond, live, subst, Continuation::Block(cond_var, body))
            }
            Expr::FunDefs {decls, body, loc: _,} => {
                // create a block name for each function
                for FunDecl { name: fun, .. } in decls.iter() {
                    let block = self.blocks.fresh(fun.hint());
                    self.fun_as_block.insert(fun.clone(), block);
                    // collect the live variables up to this point
                    self.fun_scopes.insert(fun.clone(), live.to_owned());
                }
                // lower the body
                let next = Box::new(self.lower_expr_kont(*body, live, subst, k));
                // compile the functions
                BlockBody::SubBlocks {
                    blocks: decls
                        .into_iter()
                        .filter_map(
                            |FunDecl {name: fun, params, body, loc: _,}| {
                                let live = live
                                    .to_owned()
                                    .into_iter()
                                    .chain(params.iter().map(|(p, _)| p.clone()))
                                    .collect::<Vec<_>>();
                                let block =
                                    self.fun_as_block.get(&fun).cloned().expect("fun not found");
                                if self.should_lift.contains(&fun) {
                                    // Here we need to produce a fundecl in lifted_funs,
                                    // but we need to add extra arguments.
                                    let mut subst = subst.clone();
                                    // get ambient live variables rename the ambient variables
                                    // to be unique; the ambient variables are prefixed with "@"
                                    let ambient = self
                                        .fun_scopes
                                        .get(&fun)
                                        .cloned()
                                        .expect("fun not found")
                                        .into_iter()
                                        .map(|v| {
                                            // with a hint from the previous name
                                            let new = self.vars.fresh(format!("@{}", v.hint()));
                                            subst.insert(v, new.clone());
                                            new
                                        });
                                    // get function parameters prepared
                                    let fun_params = params.into_iter().map(|(p, _)| p);
                                    // parameters are ambient live variables and the function parameters combined
                                    let params = ambient.chain(fun_params).collect::<Vec<_>>();
                                    let body = self.lower_expr_kont(body, &live, &subst, Continuation::Return,);
                                    let funblock_params = params
                                        .iter()
                                        .map(|p| self.vars.fresh(p.hint()))
                                        .collect::<Vec<_>>();
                                    let funblock = FunBlock {
                                        name: fun.clone(),
                                        params: funblock_params.clone(),
                                        body: Branch {
                                            target: block.clone(),
                                            args: funblock_params
                                                .clone()
                                                .into_iter()
                                                .map(|p| Immediate::Var(p))
                                                .collect(),
                                        },
                                    };
                                    let block = BasicBlock {
                                        label: block,
                                        params,
                                        body,
                                    };
                                    self.lifted_funs.push((funblock, block));
                                    None
                                } else {
                                    // tail recursive functions are built as sub-blocks
                                    Some(BasicBlock {
                                        label: block.clone(),
                                        params: params.into_iter().map(|(p, _)| p).collect(),
                                        body: self.lower_expr_kont(body, &live, subst, Continuation::Return),
                                    })
                                }
                            },
                        )
                        .collect(),
                    next,
                }
            }
            Expr::Call { fun, args, loc: _ } => {
                // prepare the arguments
                let (args_var, args_imm): (Vec<_>, _) = args
                    .iter()
                    .enumerate()
                    .map(|(i, _arg)| {
                        // the arguments are named after the function name and the argument index
                        let var = self.vars.fresh(format!("{}_{}", fun.hint(), i));
                        (var.clone(), Immediate::Var(var))
                    })
                    .unzip();
                let lower_call = |lowerer: &mut Lowerer, block: BlockBody| {
                    // backwards, so we need to reverse the arguments
                    args.into_iter()
                        .zip(args_var)
                        .rev()
                        .fold(block, |block, (arg, var)| {
                            lowerer.lower_expr_kont(arg, &live, subst, Continuation::Block(var, block),)
                        })
                };
                if fun.is_unmangled() {
                    // extern function. Always produce a call here
                    let (dest, next) = self.kont_to_block(k);
                    lower_call(
                        self,
                        BlockBody::Operation {
                            dest,
                            op: Operation::Call {
                                fun,
                                args: args_imm,
                            },
                            next: Box::new(next),
                        },
                    )
                } else {
                    let block = self.fun_as_block.get(&fun).cloned().expect("fun not found");
                    if self.should_lift.contains(&fun) {
                        let ambient = self
                            .fun_scopes
                            .get(&fun)
                            .cloned()
                            .expect("fun not found")
                            .into_iter()
                            .map(|v| subst.run(v));
                        // the arguments are the ambient live variables and the arguments combined
                        let args_imm = ambient
                            .map(|v| Immediate::Var(v))
                            .chain(args_imm)
                            .collect::<Vec<_>>();

                        match k {
                            Continuation::Return => lower_call(
                                self,
                                BlockBody::Terminator(Terminator::Branch(Branch {
                                    target: block,
                                    args: args_imm,
                                })),
                            ),
                            Continuation::Block(dest, next) => lower_call(
                                self,
                                BlockBody::Operation {
                                    dest,
                                    op: Operation::Call {
                                        fun,
                                        args: args_imm,
                                    },
                                    next: Box::new(next),
                                },
                            ),
                        }
                    } else {
                        // tail calls are compiled to a branch
                        assert!(matches!(k, Continuation::Return));
                        lower_call(
                            self,
                            BlockBody::Terminator(Terminator::Branch(Branch {
                                target: block,
                                args: args_imm,
                            })),
                        )
                    }
                }
            }
        }
    }
}
