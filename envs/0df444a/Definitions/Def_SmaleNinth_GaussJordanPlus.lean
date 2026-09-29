-- Prove2me | Definitions.Def_SmaleNinth_GaussJordanPlus
-- name    : SmaleNinth_GaussJordanPlus
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-24T15:37:12.346265+00:00
-- url     : https://prove2.me/theorems/b3d60de3-523b-4d91-8b4f-73e333ac5c69
-- title:
--   Rectangular complementary Gauss-Jordan-plus pivot
-- statement:
--   This definition records the complementary Gauss-Jordan-plus operation used in the source paper's pivot-pair argument. For a square real matrix $S$ and a selected index $j$, it appends the $j$-th unit column, performs a rectangular Gauss-Jordan pivot at the selected original column, swaps that column with the appended unit column, and drops the appended column. The operation is a concrete algebraic interface for the later ratio invariant; no ratio conclusion is assumed here.
-- source:
--   Samuel Awoniyi, *On pairs of complementary GJ pivoting transforming skew-symmetric matrices*, arXiv:2410.19350v1, Definition 2 and Section 3, https://arxiv.org/abs/2410.19350

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.RowCol

namespace SmaleNinth

/-- A rectangular Gauss-Jordan pivot at `(i,j)`: normalize the pivot row and
clear column `j` from every other row. Division by zero uses Lean's totalized
real division; theorem applications state the relevant pivot is nonzero. -/
noncomputable def gjPivotRect {r c : ℕ} (M : Matrix (Fin r) (Fin c) ℝ)
    (i : Fin r) (j : Fin c) : Matrix (Fin r) (Fin c) ℝ :=
  fun a b =>
    if a = i then M i b / M i j
    else M a b - M a j * (M i b / M i j)

/-- The source paper's complementary Gauss-Jordan-plus operation. Append the
selected unit column, pivot at the selected original column, swap that column
with the appended one, and drop the appended column. -/
noncomputable def gjPlus {s : ℕ} (S : Matrix (Fin s) (Fin s) ℝ) (j : Fin s) :
    Matrix (Fin s) (Fin s) ℝ :=
  let S₁ : Matrix (Fin s) (Fin (s + 1)) ℝ := fun i q =>
    Fin.lastCases (if i = j then 1 else 0) (fun k => S i k) q
  let S₂ := gjPivotRect S₁ j (Fin.castSucc j)
  fun i q =>
    if q = j then S₂ i (Fin.last s)
    else S₂ i (Fin.castSucc q)

end SmaleNinth


