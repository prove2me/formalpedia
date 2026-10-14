-- Prove2me | solution 1 for ActuarialValuation.ulProfitNPV_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:22:43.841987+00:00
-- url     : https://prove2.me/submissions/351d843c-1958-4604-8eaa-f215c7bd708f

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulProfitNPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (cash discount : ℕ → ℝ) (n : ℕ) (hc : ∀ t, 0≤cash t) (hd : ∀ t, 0≤discount t) : 0≤ulProfitNPV cash discount n := by
  unfold ulProfitNPV
  apply Finset.sum_nonneg
  intro t ht
  unfold ulDiscountedProfit
  exact mul_nonneg (hc t) (hd t)
