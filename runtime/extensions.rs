use common::*;
use std::collections::HashSet;

/* ----------------------------- Error Handling ----------------------------- */

#[repr(u64)]
pub enum SnakeErr {
    ArithmeticOverflow = 0,
    ExpectedNum = 1,
    ExpectedBool = 2,
    ExpectedArray = 3,
    NegativeLength = 4,
    IndexOutOfBounds = 5,
}

#[export_name = "\u{1}snake_error"]
pub extern "C" fn snake_error(ecode: SnakeErr, v: SnakeValue) -> SnakeValue {
    match ecode {
        SnakeErr::ArithmeticOverflow => eprintln!("arithmetic operation overflowed"),
        SnakeErr::ExpectedNum => eprintln!("expected a number, got {}", sprint_snake_val(v)),
        SnakeErr::ExpectedBool => eprintln!("expected a boolean, got {}", sprint_snake_val(v)),
        SnakeErr::ExpectedArray => eprintln!("expected an array, got {}", sprint_snake_val(v)),
        SnakeErr::NegativeLength => eprintln!("length {} is negative", sprint_snake_val(v)),
        SnakeErr::IndexOutOfBounds => eprintln!("index {} out of bounds", sprint_snake_val(v)),
    }
    std::process::exit(1)
}

/* ---------------------------- Print Snake Value --------------------------- */

/* Implement the following function for printing a snake value.
**/
pub fn sprint_snake_val(x: SnakeValue) -> String {
    let mut seen = HashSet::new();
    sprint_snake_val_rec(x, &mut seen)
}

fn sprint_snake_val_rec(x: SnakeValue, seen: &mut HashSet<u64>) -> String {
    let v = x.0;
    if v & INT_MASK == INT_TAG {
        // Int: untag by arithmetic shift right 1
        format!("{}", unsigned_to_signed(v) >> 1)
    } else if v & FULL_MASK == BOOL_TAG {
        if x == SNAKE_TRU {
            "true".to_string()
        } else {
            "false".to_string()
        }
    } else if v & FULL_MASK == ARRAY_TAG {
        let ptr = v & !FULL_MASK;
        if !seen.insert(ptr) {
            return "<loop>".to_string();
        }
        let arr = load_snake_array(ptr as *const u64);
        let elts: Vec<String> = (0..arr.size)
            .map(|i| {
                let elt = unsafe { *arr.elts.add(i as usize) };
                sprint_snake_val_rec(elt, seen)
            })
            .collect();
        seen.remove(&ptr);
        format!("[{}]", elts.join(", "))
    } else {
        format!("<unknown value: {:#x}>", v)
    }
}
