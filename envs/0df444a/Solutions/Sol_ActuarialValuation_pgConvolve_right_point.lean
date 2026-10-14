-- Prove2me | solution 1 for ActuarialValuation.pgConvolve_right_point
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:34:37.261436+00:00
-- url     : https://prove2.me/submissions/60b2b4bb-c0ac-4d34-8e13-3ff585088d24

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgPointMass
import Definitions.Def_actuarial_pgConvolve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (k : ℕ) : pgConvolve f pgPointMass k = f k := by
  unfold pgConvolve
  rw [Finset.sum_eq_single k]
  · simp [pgPointMass]
  · intro j hj hne
    have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hjlt : j < k := lt_of_le_of_ne hjle hne
    have hsub : k - j ≠ 0 := ne_of_gt (Nat.sub_pos_of_lt hjlt)
    simp [pgPointMass, hsub]
  · simp
