-- Prove2me | solution 1 for ActuarialAnnuities.survival_decrement
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:16:22.336414+00:00
-- url     : https://prove2.me/submissions/dc46a147-6d82-4e54-9c9c-6bd8c3407917

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvival
open ActuarialAnnuities

theorem solution(h t : ℕ) (p : ℕ → ℝ) (ht : t ≤ h) : bSurvival h p t = p t + bSurvival h p (t+1) := by
  unfold bSurvival bAlive
  rw [← sub_eq_iff_eq_add, ← Finset.sum_sub_distrib]
  have key : ∀ k ∈ Finset.range (h+1), (p k * (if t ≤ k then 1 else 0) - p k * (if t+1 ≤ k then 1 else 0) : ℝ) = if k = t then p k else 0 := by
    intro k _
    by_cases h1 : k = t
    · subst h1; simp
    · by_cases h2 : t ≤ k
      · rw [if_pos h2, if_pos (by omega), if_neg h1]; ring
      · rw [if_neg h2, if_neg (by omega), if_neg h1]; ring
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq']
  rw [if_pos (by simp; omega)]
