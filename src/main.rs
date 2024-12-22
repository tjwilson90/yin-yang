use std::iter;

use z3::ast::Ast;
use z3::ast::Bool;
use z3::ast::Int;
use z3::Config;
use z3::Context;
use z3::SatResult;
use z3::Solver;

fn main() {
    let Some(puzzle) = std::env::args().nth(1) else {
        eprintln!("Usage: ./yin-yang <puzzle>");
        return;
    };
    
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);
    let cells = make_cells(&ctx, &puzzle);

    assert_blocks(&solver, &cells);
    assert_boundary(&solver, &cells);
    assert_connectivity(&solver, &cells, false);
    assert_connectivity(&solver, &cells, true);
    print_solution(&solver, &cells);
}

// make cells and assert initial conditions
fn make_cells<'a>(ctx: &'a Context, puzzle: &str) -> Vec<Bool<'a>> {
    let mut cells = vec![];
    for ch in puzzle.chars() {
        if ch == 'B' {
            cells.push(Bool::from_bool(&ctx, false));
        } else if ch == 'W' {
            cells.push(Bool::from_bool(&ctx, true));
        } else {
            let blanks = 1 + (ch as usize) - ('a' as usize);
            cells.extend(iter::repeat_with(|| Bool::fresh_const(&ctx, "")).take(blanks));
        }
    }
    cells
}

// no 2x2 squares or 2x2 criss crosses
fn assert_blocks(solver: &Solver<'_>, cells: &[Bool<'_>]) {
    let ctx = solver.get_context();
    let size = (cells.len() as f64).sqrt() as usize;
    for i in 0..size-1 {
        for j in 0..size-1 {
            let tl = &cells[i*size + j];
            let tr = &cells[i*size + j+1];
            let bl = &cells[(i+1)*size + j];
            let br = &cells[(i+1)*size + j+1];
            solver.assert(&Bool::and(&ctx, &[tl, tr, bl, br]).not());
            solver.assert(&Bool::or(&ctx, &[tl, tr, bl, br]));
            solver.assert(&Bool::and(&ctx, &[tl, &tr.not(), &bl.not(), br]).not());
            solver.assert(&Bool::and(&ctx, &[&tl.not(), tr, bl, &br.not()]).not());
        }
    }
}

// boundary can change from white to black or vice versa at most twice
fn assert_boundary(solver: &Solver<'_>, cells: &[Bool<'_>]) {
    let ctx = solver.get_context();
    let size = (cells.len() as f64).sqrt() as usize;
    let mut boundary = vec![];
    for i in 0..size-1 {
        let tl = &cells[i*size];
        let tr = &cells[i*size + size-1];
        let bl = &cells[(i+1)*size];
        let br = &cells[(i+1)*size + size-1];
        boundary.push(tl._eq(bl).not());
        boundary.push(tr._eq(br).not());
    }
    for j in 0..size-1 {
        let tl = &cells[j];
        let tr = &cells[j+1];
        let bl = &cells[(size-1)*size + j];
        let br = &cells[(size-1)*size + j+1];
        boundary.push(tl._eq(tr).not());
        boundary.push(bl._eq(br).not());
    }
    let boundary = boundary.iter().map(|cond| (cond, 1)).collect::<Vec<_>>();
    solver.assert(&Bool::pb_le(&ctx, &boundary, 2));

}

// all squares of the same color must be connected
fn assert_connectivity(solver: &Solver<'_>, cells: &[Bool<'_>], color: bool) {
    let ctx = solver.get_context();
    let zero = Int::from_u64(&ctx, 0);
    let infinity = Int::from_u64(&ctx, cells.len() as u64);
    let size = (cells.len() as f64).sqrt() as usize;
    let dists = iter::repeat_with(|| Int::fresh_const(&ctx, "")).take(cells.len()).collect::<Vec<_>>();
    let root = cells.iter().position(|cell| cell.as_bool() == Some(color)).unwrap();
    for i in 0..size {
        for j in 0..size {
            let idx = i*size + j;
            let dist = &dists[idx];
            if idx == root {
                solver.assert(&dist._eq(&zero));
                continue;
            }
            
            let mut conditions = vec![];
            if i > 0 {
                conditions.push(dist.gt(&dists[(i-1)*size + j]));
            }
            if i < size-1 {
                conditions.push(dist.gt(&dists[(i+1)*size + j]));
            }
            if j > 0 {
                conditions.push(dist.gt(&dists[i*size + j-1]));
            }
            if j < size-1 {
                conditions.push(dist.gt(&dists[i*size + j+1]));
            }
            let conditions = conditions.iter().collect::<Vec<_>>();
            let dist_if_eq = Bool::or(&ctx, &conditions);
            let cond_if_eq = Bool::and(&ctx, &[&dist_if_eq, &dist.lt(&infinity)]);
            let cond_if_ne = dist._eq(&infinity);
            solver.assert(&cells[idx]._eq(&cells[root]).ite(&cond_if_eq, &cond_if_ne));
        }
    }
}

fn print_solution(solver: &Solver<'_>, cells: &[Bool<'_>]) {
    let size = (cells.len() as f64).sqrt() as usize;
    assert_eq!(solver.check(), SatResult::Sat);
    let model = solver.get_model().unwrap();
    for i in 0..size {
        for j in 0..size {
            let bool = model.eval(&cells[i*size + j], true).unwrap();
            if bool.as_bool().unwrap() {
                print!("⚪");
            } else {
                print!("⚫");
            }
        }
        println!();
    }
}