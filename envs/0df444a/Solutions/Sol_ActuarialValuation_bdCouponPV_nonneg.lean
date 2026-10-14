-- Prove2me | solution 1 for ActuarialValuation.bdCouponPV_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:58:08.761627+00:00
-- url     : https://prove2.me/submissions/ba7c6394-2aaf-49a8-9827-cb4da483d5fc

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdCouponPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D c : ℕ → ℝ) (n : ℕ) (hD : ∀ k∈Finset.range n, 0≤D (k+1)) (hc : ∀ k∈Finset.range n, 0≤c k) : 0≤bdCouponPV D c n := by
  unfold bdCouponPV
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (hc k hk) (hD k hk)
