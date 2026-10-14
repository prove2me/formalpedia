-- Prove2me | solution 1 for ActuarialValuation.pgConvolve_left_point
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:33:17.388809+00:00
-- url     : https://prove2.me/submissions/9b284ae7-341e-47b6-b6d0-69b8297ccffd

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgPointMass
import Definitions.Def_actuarial_pgConvolve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (k : ℕ) : pgConvolve pgPointMass f k = f k := by
  unfold pgConvolve
  rw [Finset.sum_eq_single 0]
  · simp [pgPointMass]
  · intro j hj hne
    simp [pgPointMass, hne]
  · simp
