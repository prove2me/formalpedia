-- Prove2me | solution 1 for ActuarialValuation.pgFold_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:27:48.960393+00:00
-- url     : https://prove2.me/submissions/48f00972-17eb-4f77-bdc2-19a52f204cb6

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgFold
open ActuarialValuation

theorem solution(f : ℕ → ℝ) (k : ℕ) : pgFold f 1 k = f k := by
  show pgConvolve f pgPointMass k = f k
  unfold pgConvolve
  rw [Finset.sum_eq_single k]
  · simp [pgPointMass]
  · intro b hb hbk
    rw [Finset.mem_range] at hb
    have : k - b ≠ 0 := by omega
    simp [pgPointMass, this]
  · intro hk
    exfalso; apply hk; rw [Finset.mem_range]; omega
