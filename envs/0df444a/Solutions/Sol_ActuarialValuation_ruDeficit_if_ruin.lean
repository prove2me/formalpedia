-- Prove2me | solution 1 for ActuarialValuation.ruDeficit_if_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:22:48.788601+00:00
-- url     : https://prove2.me/submissions/70558b24-c795-4b2b-be4e-0de75d885238

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruPathSurplus
import Definitions.Def_actuarial_ruRuinAt
import Definitions.Def_actuarial_ruDeficit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u c : ℝ) (x : ℕ → ℝ) (n : ℕ)
    (h : ruRuinAt u c x n) :
    ruDeficit u c x n = -ruPathSurplus u c x n := by
  unfold ruRuinAt at h
  unfold ruDeficit
  exact max_eq_right (le_of_lt (neg_pos.mpr h))
