-- Prove2me | solution 1 for ActuarialAnnuities.survival_mono
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:07:47.105997+00:00
-- url     : https://prove2.me/submissions/2e3b6c30-345f-4e85-9418-116a0508c8dd

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvival
open ActuarialAnnuities

theorem solution(h t u : ℕ) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (htu : t ≤ u) : bSurvival h p u ≤ bSurvival h p t := by
  unfold bSurvival
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left _ (hp k)
  unfold bAlive
  by_cases h1 : u ≤ k
  · rw [if_pos h1, if_pos (le_trans htu h1)]
  · rw [if_neg h1]
    split_ifs <;> norm_num
