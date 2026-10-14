-- Prove2me | solution 1 for ActuarialValuation.mackVarianceNumerator_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:36:10.405185+00:00
-- url     : https://prove2.me/submissions/e4feecec-11f9-43f0-99df-3cedc0073356

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackVarianceNumerator

import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b e : ℕ → ℝ) (m : ℕ) (h : ∀ i ∈ Finset.range m, 0 < e i) : 0 ≤ mackVarianceNumerator a b e m := by
  unfold mackVarianceNumerator
  apply Finset.sum_nonneg
  intro i hi
  unfold mackScaledResidual mackSquaredResidual
  exact div_nonneg (sq_nonneg _) (le_of_lt (h i hi))
