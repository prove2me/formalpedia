-- Prove2me | solution 1 for ActuarialValuation.mackDenominator_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:31:42.280843+00:00
-- url     : https://prove2.me/submissions/165a07f6-fe39-44a7-ae49-de8df861d625

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackDenominator
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℕ → ℝ) (m j : ℕ) (h : ∀ i ∈ Finset.range m, 0 ≤ c i j) : 0 ≤ mackDenominator c m j := by
  unfold mackDenominator
  exact Finset.sum_nonneg (fun i hi => h i hi)
