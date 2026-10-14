-- Prove2me | solution 1 for ActuarialAnnuities.path_expectation_reconciliation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:51:18.636448+00:00
-- url     : https://prove2.me/submissions/74d3dbda-7b0f-40ae-9e0a-650d46fef2c6

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bExpectedPV
import Definitions.Def_actuarial_bSurvivalPV
open ActuarialAnnuities

theorem solution(h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) : bExpectedPV h a n g delta v b p = bSurvivalPV h a n g delta v b p := by
  unfold bExpectedPV bSurvivalPV bPathPV bSurvival bEntitlement
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> first | (simp; done) | (rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring) | (apply Finset.sum_congr rfl; intro k _; ring)
