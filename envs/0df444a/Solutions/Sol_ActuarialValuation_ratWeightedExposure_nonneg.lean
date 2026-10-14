-- Prove2me | solution 1 for ActuarialValuation.ratWeightedExposure_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:28:45.190899+00:00
-- url     : https://prove2.me/submissions/2bd473c3-1a06-43fc-ad0b-0aa5010940d0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_ratWeightedExposure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (e r : ℕ → ℝ) (n : ℕ)
    (he : ∀ i ∈ Finset.range n, 0 ≤ e i)
    (hr : ∀ i ∈ Finset.range n, 0 ≤ r i) :
    0 ≤ ratWeightedExposure e r n := by
  unfold ratWeightedExposure
  exact Finset.sum_nonneg fun i hi => mul_nonneg (he i hi) (hr i hi)
