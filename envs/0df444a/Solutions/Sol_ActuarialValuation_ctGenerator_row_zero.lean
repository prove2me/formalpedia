-- Prove2me | solution 1 for ActuarialValuation.ctGenerator_row_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:17:34.632149+00:00
-- url     : https://prove2.me/submissions/2a0e1407-4df4-4114-8371-7daaa3aaac32

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctGenerator
open ActuarialValuation

theorem solution(r : Fin 3 → Fin 3 → ℝ) (i : Fin 3) : (∑ j : Fin 3, ctGenerator r i j) = 0 := by
  fin_cases i <;> simp [Fin.sum_univ_three, ctGenerator, ctRateOut] <;> ring
