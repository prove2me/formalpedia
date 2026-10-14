-- Prove2me | solution 2 for ActuarialAnnuities.precommencement_death
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T13:11:49.696009+00:00
-- url     : https://prove2.me/submissions/208c4d39-d74a-4286-8a76-b9b9414a0449

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bPathPV
open ActuarialAnnuities

theorem solution (h a n g delta k : ℕ) (v : ℝ) (b : ℕ → ℝ) (hk : k < a) : bPathPV h a n g delta v b k = 0 := by
  simp only [bPathPV, bEntitlement, bAlive]
  apply Finset.sum_eq_zero
  intro j _
  split_ifs <;> simp [not_le_of_gt hk] <;> omega

