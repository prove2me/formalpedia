-- Prove2me | solution 1 for ActuarialAnnuities.fractional_random_expectation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T10:14:30.344045+00:00
-- url     : https://prove2.me/submissions/8d918e4a-b629-4ee9-8bcd-be84d53805e3

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bFractionalExpectedPV
import Definitions.Def_actuarial_bFractionalSurvivalPV
open ActuarialAnnuities

theorem solution(h a n g delta m : ℕ) (w : ℝ) (b p : ℕ → ℝ) : bFractionalExpectedPV h a n g delta m w b p = bFractionalSurvivalPV h a n g delta m w b p := by
  unfold bFractionalExpectedPV bFractionalSurvivalPV
  unfold bExpectedPV bSurvivalPV bPathPV bSurvival bEntitlement
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> first | (simp; done) | (rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring) | (apply Finset.sum_congr rfl; intro k _; ring)
