-- Prove2me | solution 1 for ActuarialValuation.ratExposureSum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:27:38.447438+00:00
-- url     : https://prove2.me/submissions/5306644a-905a-4a84-953b-122abd612065

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_ratExposureSum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (e : ℕ → ℝ) (n : ℕ)
    (he : ∀ i ∈ Finset.range n, 0 ≤ e i) :
    0 ≤ ratExposureSum e n := by
  unfold ratExposureSum
  exact Finset.sum_nonneg fun i hi => he i hi
