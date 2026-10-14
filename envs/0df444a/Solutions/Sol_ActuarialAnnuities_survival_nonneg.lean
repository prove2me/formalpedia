-- Prove2me | solution 1 for ActuarialAnnuities.survival_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T07:28:02.72926+00:00
-- url     : https://prove2.me/submissions/f89ee877-a63d-4fe4-ba25-8c11b86bfdb5

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvival
open ActuarialAnnuities

theorem solution(h t : ℕ) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) : 0 ≤ bSurvival h p t := by
  unfold bSurvival
  apply Finset.sum_nonneg
  intro k _
  unfold bAlive
  split_ifs <;> simp [hp k]
