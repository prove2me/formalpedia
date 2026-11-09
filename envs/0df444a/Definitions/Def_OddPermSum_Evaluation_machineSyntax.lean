-- Prove2me | Definitions.Def_OddPermSum_Evaluation_machineSyntax
-- name    : OddPermSum_Evaluation_machineSyntax
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:09:50.500199+00:00
-- url     : https://prove2.me/theorems/c1db8665-587d-4967-b07c-c51b364cdd28
-- title:
--   Finite algebraic programs with integer control
-- statement:
--   A program is finite syntax for indexed field-register operations, input and copy, constants, addition, subtraction, multiplication, guarded inversion, zero tests, output, sequencing, branches, and loops. Integer expressions use the dimension, integer registers, and explicit natural-number arithmetic and comparisons; they cannot read field registers.
--
--   $$\text{field access}=\{\text{constants, input, copy},+,-,\times,\text{inverse, zero test, output}\}.$$
--
--   Constants are finitely many field elements occurring in the program, fixed before any matrix input. There is no arbitrary-function instruction, encoding of field values as integers, determinant, inverse-matrix, rank, matrix-multiplication, or gradient primitive. This is the operational encoding of the paper's field-operation model, reusable outside this mission.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 5, Linear algebra cost convention; p. 2, Theorem 1.1 (operational encoding)

import Mathlib

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- Integer control expressions. They have no access to field memory. -/
inductive IndexExpr where
  | literal : ℕ → IndexExpr
  | dimension : IndexExpr
  | read : IndexExpr → IndexExpr
  | add : IndexExpr → IndexExpr → IndexExpr
  | sub : IndexExpr → IndexExpr → IndexExpr
  | mul : IndexExpr → IndexExpr → IndexExpr
  | div : IndexExpr → IndexExpr → IndexExpr
  | mod : IndexExpr → IndexExpr → IndexExpr
  | less : IndexExpr → IndexExpr → IndexExpr
  | equal : IndexExpr → IndexExpr → IndexExpr

/-- A finite algebraic program. Arrays are indexed registers. No function-valued
instruction, matrix primitive, or field-to-integer encoding occurs in the syntax. -/
inductive AlgebraicProgram (F : Type*) where
  | skip : AlgebraicProgram F
  | setIndex : IndexExpr → IndexExpr → AlgebraicProgram F
  | constant : IndexExpr → F → AlgebraicProgram F
  | input : IndexExpr → IndexExpr → AlgebraicProgram F
  | copy : IndexExpr → IndexExpr → AlgebraicProgram F
  | add : IndexExpr → IndexExpr → IndexExpr → AlgebraicProgram F
  | sub : IndexExpr → IndexExpr → IndexExpr → AlgebraicProgram F
  | mul : IndexExpr → IndexExpr → IndexExpr → AlgebraicProgram F
  | inverse : IndexExpr → IndexExpr → AlgebraicProgram F
  | zeroTest : IndexExpr → IndexExpr → AlgebraicProgram F
  | output : IndexExpr → AlgebraicProgram F
  | sequence : AlgebraicProgram F → AlgebraicProgram F → AlgebraicProgram F
  | branch : IndexExpr → AlgebraicProgram F → AlgebraicProgram F → AlgebraicProgram F
  | loop : IndexExpr → AlgebraicProgram F → AlgebraicProgram F

end OddPermSum.Evaluation


