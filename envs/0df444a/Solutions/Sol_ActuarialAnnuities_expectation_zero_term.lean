-- Prove2me | solution 1 for ActuarialAnnuities.expectation_zero_term
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:16:02.296167+00:00
-- url     : https://prove2.me/submissions/781c27c6-2a17-4ad4-8b7e-1899f954115b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bExpectedPV
open ActuarialAnnuities

theorem solution(h a g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) : bExpectedPV h a 0 g delta v b p = 0 := by
  unfold bExpectedPV
  apply Finset.sum_eq_zero
  intro k _
  unfold bPathPV
  rw [Finset.sum_eq_zero (fun j _ => if_neg (by omega))]
  ring
