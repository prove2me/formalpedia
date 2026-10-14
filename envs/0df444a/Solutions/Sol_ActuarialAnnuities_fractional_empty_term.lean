-- Prove2me | solution 1 for ActuarialAnnuities.fractional_empty_term
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:33:38.239992+00:00
-- url     : https://prove2.me/submissions/fbfaf85d-cef4-4c7e-b653-eafe019a2787

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bFractionalExpectedPV
open ActuarialAnnuities

theorem solution(h a g delta m : ℕ) (w : ℝ) (b p : ℕ → ℝ) : bFractionalExpectedPV h a 0 g delta m w b p = 0 := by
  unfold bFractionalExpectedPV
  simp only [zero_mul]
  unfold bExpectedPV
  apply Finset.sum_eq_zero
  intro k _
  unfold bPathPV
  rw [Finset.sum_eq_zero (fun j _ => if_neg (by omega))]
  ring
