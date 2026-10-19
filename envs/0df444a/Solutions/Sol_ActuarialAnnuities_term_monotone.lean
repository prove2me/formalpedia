-- Prove2me | solution 1 for ActuarialAnnuities.term_monotone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:08:09.354512+00:00
-- url     : https://prove2.me/submissions/f93a6859-d0fe-4edc-91fe-ed4350defd58

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvivalPV

open ActuarialAnnuities

theorem solution (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hv : 0 ≤ v) (hb : ∀ j, 0 ≤ b j) (hp : ∀ k, 0 ≤ p k) : bSurvivalPV h a n g delta v b p ≤ bSurvivalPV h a (n+1) g delta v b p := by
  have hS : ∀ t, 0 ≤ bSurvival h p t := fun t => Finset.sum_nonneg (fun k _ => mul_nonneg (hp k) (by unfold bAlive; split_ifs <;> norm_num))
  unfold bSurvivalPV; apply Finset.sum_le_sum; intro j _
  split_ifs <;> first | (exfalso; omega) | exact le_rfl | (apply mul_nonneg (mul_nonneg (hb j) (pow_nonneg hv _)); exact hS _)

