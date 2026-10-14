-- Prove2me | solution 1 for ActuarialValuation.pucAccruedBenefit_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:04:42.212569+00:00
-- url     : https://prove2.me/submissions/9f51449f-9a4c-4ed5-8b84-3a7d5b6aa031

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_pucAccruedBenefit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u : ℕ → ℝ) (n : ℕ) (hu : ∀ t ∈ Finset.range n, 0 ≤ u t) : 0 ≤ pucAccruedBenefit u n := by
  unfold pucAccruedBenefit
  exact Finset.sum_nonneg (fun t ht => hu t ht)
