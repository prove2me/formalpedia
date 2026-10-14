-- Prove2me | solution 1 for ActuarialValuation.ctEuler_row_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:52:06.362979+00:00
-- url     : https://prove2.me/submissions/9f14e511-316c-497b-8dd1-ab4f99d56a76

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctEuler
open ActuarialValuation

theorem solution(r : Fin 3 → Fin 3 → ℝ) (h : ℝ) (i : Fin 3) : (∑ j : Fin 3, ctEuler r h i j) = 1 := by
  fin_cases i <;> simp [Fin.sum_univ_three, ctEuler, ctGenerator, ctRateOut] <;> ring
