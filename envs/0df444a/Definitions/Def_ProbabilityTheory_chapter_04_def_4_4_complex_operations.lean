-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_04_def_4_4_complex_operations
-- name    : ProbabilityTheory_chapter_04_def_4_4_complex_operations
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T08:00:01.102877+00:00
-- url     : https://prove2.me/theorems/b3de4856-01bb-4d38-861a-918a0056bdf1
-- title:
--   Chapter ?, generated supplement: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter ?, source module `generated supplement`: `complex_addition_equivalence`, `complex_abs`, `complex_triangle_inequality`, `complex_multiplication_equivalence`, `complex_conjugate`, and 1 others. The mathematical interpretation of this bundle needs review.
-- source:
--   Supplemental source module in importer v37; upstream repository https://github.com/wkshum/ProbabilityTheory/tree/e6387d4fd8005d627d2aec40d10f039ddb4e4b40

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic

theorem complex_addition_equivalence (a b c d : ℝ) :
    Complex.mk a b + Complex.mk c d = Complex.mk (a + c) (b + d) := rfl

noncomputable def complex_abs (z : ℂ) : ℝ := Norm.norm z

local notation "|" z "|" => complex_abs z

theorem complex_triangle_inequality (z1 z2 : ℂ) :
    |z1 + z2| ≤ |z1| + |z2| :=
  norm_add_le z1 z2

theorem complex_multiplication_equivalence (a b c d : ℝ) :
    Complex.mk a b * Complex.mk c d = Complex.mk (a * c - b * d) (a * d + b * c) := rfl

def complex_conjugate (z : ℂ) : ℂ :=
  ⟨z.re, -z.im⟩

postfix:max "∗" => complex_conjugate

theorem complex_conjugate_spec (a b : ℝ) :
    (Complex.mk a b)∗ = Complex.mk a (-b) := rfl


