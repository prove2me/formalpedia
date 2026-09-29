-- Prove2me | Definitions.Def_SmaleNinth_GaussJordanPivot
-- name    : SmaleNinth_GaussJordanPivot
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-24T12:44:56.754273+00:00
-- url     : https://prove2.me/theorems/b9305ac2-7483-4822-bab1-3a1b0bc23a49
-- title:
--   Complementary Gauss-Jordan pivot operations
-- statement:
--   This definition supplies the elementary row operations used by the complementary Gauss-Jordan pivot algorithm: normalize a pivot row, clear its pivot column from the other rows, add the last row to the first row, and compose the fixed 5-by-5 pair of pivots. It is the machine-independent algebraic core used by the certificate-producing real-RAM solver.
-- source:
--   Samuel Awoniyi, *On pairs of complementary GJ pivotings transforming skew-symmetric matrices*, arXiv:2410.19350v1, Section 2, Lemma 1, https://arxiv.org/abs/2410.19350

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.RowCol

namespace SmaleNinth

/-- A Gauss-Jordan pivot at `(r,c)`: normalize the pivot row and clear column `c`
from every other row. Division by zero uses Lean's totalized real division;
all theorem applications below state the relevant pivot is nonzero. -/
noncomputable def gjPivot {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (r c : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    if i = r then M r j / M r c
    else M i j - M i c * (M r j / M r c)

/-- The fixed 5-by-5 paired operation used in the first complementary-pivot
case: add the last row to the first row, then pivot at `(0,0)` and `(3,3)`. -/
noncomputable def pairedPivot5 (S : Matrix (Fin 5) (Fin 5) ℝ) :
    Matrix (Fin 5) (Fin 5) ℝ :=
  gjPivot
    (gjPivot (S.updateRow 0 (fun j => S 0 j + S 4 j)) 0 0)
    3 3

end SmaleNinth


