-- Prove2me | solution 1 for ActuarialValuation.pen9TargetCapital_annuity_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:23:18.63641+00:00
-- url     : https://prove2.me/submissions/eb708c08-b308-4a46-bec4-64daf03ec1ff

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9TargetCapital

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (s ratio a₁ a₂ : ℝ) (hs : 0 ≤ s) (hr : 0 ≤ ratio) (ha : a₁ ≤ a₂) : pen9TargetCapital s ratio a₁ ≤ pen9TargetCapital s ratio a₂ := by
  unfold pen9TargetCapital
  exact mul_le_mul_of_nonneg_left ha (mul_nonneg hr hs)
