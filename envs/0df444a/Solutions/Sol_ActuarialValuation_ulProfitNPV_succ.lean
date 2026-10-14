-- Prove2me | solution 1 for ActuarialValuation.ulProfitNPV_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:23:39.636122+00:00
-- url     : https://prove2.me/submissions/8424125d-03f2-4abb-9d41-9767c7afe6c7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulDiscountedProfit
import Definitions.Def_actuarial_ulProfitNPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (cash discount : ℕ → ℝ) (n : ℕ) : ulProfitNPV cash discount (n+1)=ulProfitNPV cash discount n+ulDiscountedProfit (cash n) (discount n) := by
  unfold ulProfitNPV
  rw [Finset.sum_range_succ]
