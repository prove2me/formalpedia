-- Prove2me | solution 1 for ActuarialValuation.ratRevenueSurplus_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:35:48.698008+00:00
-- url     : https://prove2.me/submissions/10bb3f40-f414-42f2-96b6-e66284b9e44e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratRevenueSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (target w b1 b2 : ℝ) (hw : 0 ≤ w) (h : b1 ≤ b2) : ratRevenueSurplus target w b1 ≤ ratRevenueSurplus target w b2 := by
  unfold ratRevenueSurplus
  exact sub_le_sub_right (mul_le_mul_of_nonneg_right h hw) target
