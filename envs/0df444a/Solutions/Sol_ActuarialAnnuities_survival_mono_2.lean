-- Prove2me | solution 2 for ActuarialAnnuities.survival_mono
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T13:09:13.499295+00:00
-- url     : https://prove2.me/submissions/5b6380a1-4bab-4835-90e7-1ac7ac4cb0f0

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvival
open ActuarialAnnuities

theorem solution (h t u : ℕ) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (htu : t ≤ u) : bSurvival h p u ≤ bSurvival h p t := by
  simp only [bSurvival, bAlive]
  apply Finset.sum_le_sum
  intro k _
  split_ifs with hu ht ht
  · simp
  · exact absurd (le_trans htu hu) ht
  · simpa using hp k
  · simp

