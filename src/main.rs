use ArithCmpOp::*;
use ArithExpr::*;
use BinArithOp::*;
use BinLogicOp::*;
use BoolExpr::*;
use Expr::*;
use Value::*;

pub enum Expr {
    ArithExpr(ArithExpr),
    BoolExpr(BoolExpr),
}

pub enum ArithExpr {
    BinArithExpr {
        left: Box<ArithExpr>,
        right: Box<ArithExpr>,
        op: BinArithOp,
    },
    IntLit(i64),
}

pub enum BoolExpr {
    ArithCmpExpr {
        left: Box<ArithExpr>,
        right: Box<ArithExpr>,
        op: ArithCmpOp,
    },
    BinBoolExpr {
        left: Box<BoolExpr>,
        right: Box<BoolExpr>,
        op: BinLogicOp,
    },
    NotExpr(Box<BoolExpr>),
    BoolLit(bool),
}

pub enum BinArithOp {
    AddOp,
    SubOp,
    MulOp,
    IntDivOp,
}

pub enum ArithCmpOp {
    LtOp,
    LteOp,
    GtOp,
    GteOp,
    ArithEqOp,
    ArithNeqOp,
}

pub enum BinLogicOp {
    AndOp,
    OrOp,
    BoolEqOp,
    BoolNeqOp,
}

#[derive(Debug, PartialEq)]
pub enum Value {
    BoolValue(bool),
    IntValue(i64),
}

// #[derive(Debug)]
// enum Expr {
//     NotExpr(Box<Expr>),
//     OrExpr { left: Box<Expr>, right: Box<Expr> },
//     AndExpr { left: Box<Expr>, right: Box<Expr> },
//     IntExpr(u8),
// }

// fn eval_bitwise_expr(expr: Expr) -> u8 {
//     use Expr::*;

//     match expr {
//         NotExpr(expr) => !eval_bitwise_expr(*expr),
//         OrExpr { left, right } => eval_bitwise_expr(*left) | eval_bitwise_expr(*right),
//         AndExpr { left, right } => eval_bitwise_expr(*left) & eval_bitwise_expr(*right),
//         IntExpr(num) => num,
//     }
// }

// Required functions
pub fn eval(expr: Expr) -> Value {
    match expr {
        ArithExpr(arith_expr) => Value::IntValue(eval_arith_expr(arith_expr)),
        BoolExpr(bool_expr) => Value::BoolValue(eval_bool_expr(bool_expr)),
    }
}

pub fn eval_arith_expr(arith_expr: ArithExpr) -> i64 {
    match arith_expr {
        BinArithExpr { left, right, op } => match op {
            AddOp => eval_arith_expr(*left) + eval_arith_expr(*right),
            SubOp => eval_arith_expr(*left) - eval_arith_expr(*right),
            MulOp => eval_arith_expr(*left) * eval_arith_expr(*right),
            IntDivOp => eval_arith_expr(*left) / eval_arith_expr(*right),
        },
        IntLit(value) => value,
    }
}

pub fn eval_bool_expr(bool_expr: BoolExpr) -> bool {
    match bool_expr {
        ArithCmpExpr { left, right, op } => match op {
            LtOp => eval_arith_expr(*left) < eval_arith_expr(*right),
            LteOp => eval_arith_expr(*left) <= eval_arith_expr(*right),
            GtOp => eval_arith_expr(*left) > eval_arith_expr(*right),
            GteOp => eval_arith_expr(*left) >= eval_arith_expr(*right),
            ArithEqOp => eval_arith_expr(*left) == eval_arith_expr(*right),
            ArithNeqOp => eval_arith_expr(*left) != eval_arith_expr(*right),
        },
        BinBoolExpr { left, right, op } => match op {
            AndOp => eval_bool_expr(*left) && eval_bool_expr(*right),
            OrOp => eval_bool_expr(*left) || eval_bool_expr(*right),
            BoolEqOp => eval_bool_expr(*left) == eval_bool_expr(*right),
            BoolNeqOp => eval_bool_expr(*left) != eval_bool_expr(*right),
        },

        NotExpr(inner_bool_expr) => !(eval_bool_expr(*inner_bool_expr)),
        BoolLit(bool_lit) => bool_lit,
    }
}

fn main() {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sample() {
        let expr = BoolExpr(BoolLit(true));
        let answer = BoolValue(true);

        assert_eq!(eval(expr), answer); // eval(BoolExpr(BoolLit(true))) == BoolValue(true)
    }

    #[test]
    fn test_others() {
        main();
        println!("{:?}", BoolValue(true));
    }

    #[test]
    fn test() {
        let bool_expr_and_or_eq: Expr = BoolExpr(BinBoolExpr {
            left: Box::new(BinBoolExpr {
                left: Box::new(BoolExpr::BoolLit(true)),
                right: Box::new(BoolExpr::BoolLit(true)),
                op: AndOp,
            }),
            right: Box::new(BinBoolExpr {
                left: Box::new(BoolExpr::BoolLit(false)),
                right: Box::new(BoolExpr::BoolLit(false)),
                op: OrOp,
            }),
            op: BoolEqOp,
        });
        let answer_1: Value = BoolValue(false);
        assert_eq!(eval(bool_expr_and_or_eq), answer_1);

        let bool_expr_arith_lt_lte_neq: Expr = BoolExpr(BinBoolExpr {
            left: Box::new(ArithCmpExpr {
                left: Box::new(ArithExpr::IntLit(1)),
                right: Box::new(ArithExpr::IntLit(1000)),
                op: LtOp,
            }),
            right: Box::new(ArithCmpExpr {
                left: Box::new(ArithExpr::IntLit(1)),
                right: Box::new(ArithExpr::IntLit(1)),
                op: LteOp,
            }),
            op: BoolNeqOp,
        });
        let answer_2: Value = BoolValue(false);
        assert_eq!(eval(bool_expr_arith_lt_lte_neq), answer_2);

        let bool_expr_arith_gt_gte_neq: Expr = BoolExpr(BinBoolExpr {
            left: Box::new(ArithCmpExpr {
                left: Box::new(ArithExpr::IntLit(1000)),
                right: Box::new(ArithExpr::IntLit(1)),
                op: GtOp,
            }),
            right: Box::new(ArithCmpExpr {
                left: Box::new(ArithExpr::IntLit(1)),
                right: Box::new(ArithExpr::IntLit(1)),
                op: GteOp,
            }),
            op: BoolNeqOp,
        });
        let answer_3: Value = BoolValue(false);
        assert_eq!(eval(bool_expr_arith_gt_gte_neq), answer_3);

        let bool_expr_arith_neq_eq: Expr = BoolExpr(BinBoolExpr {
            left: Box::new(ArithCmpExpr {
                left: Box::new(ArithExpr::IntLit(1)),
                right: Box::new(ArithExpr::IntLit(1000)),
                op: ArithEqOp,
            }),
            right: Box::new(ArithCmpExpr {
                left: Box::new(ArithExpr::IntLit(1)),
                right: Box::new(ArithExpr::IntLit(1)),
                op: ArithNeqOp,
            }),
            op: BoolNeqOp,
        });
        let answer_4: Value = BoolValue(false);
        assert_eq!(eval(bool_expr_arith_neq_eq), answer_4);

        let arith_add_sub_mul: Expr = ArithExpr(BinArithExpr {
            left: Box::new(BinArithExpr {
                left: Box::new(ArithExpr::IntLit(3)),
                right: Box::new(ArithExpr::IntLit(5)),
                op: AddOp,
            }),
            right: Box::new(BinArithExpr {
                left: Box::new(ArithExpr::IntLit(2)),
                right: Box::new(ArithExpr::IntLit(1)),
                op: SubOp,
            }),
            op: MulOp,
        });
        let answer_5: Value = IntValue(8);
        assert_eq!(eval(arith_add_sub_mul), answer_5);

        let arith_div: Expr = ArithExpr(BinArithExpr {
            left: Box::new(ArithExpr::IntLit(2)),
            right: Box::new(ArithExpr::IntLit(2)),
            op: IntDivOp,
        });
        let answer_6: Value = IntValue(1);
        assert_eq!(eval(arith_div), answer_6);

        let bool_not: Expr = BoolExpr(NotExpr(Box::new(BoolExpr::BoolLit(true))));
        let answer_7: Value = BoolValue(false);
        assert_eq!(eval(bool_not), answer_7);
    }
}
