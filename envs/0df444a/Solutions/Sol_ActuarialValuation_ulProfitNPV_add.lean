-- Prove2me | solution 1 for ActuarialValuation.ulProfitNPV_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:23:27.585044+00:00
-- url     : https://prove2.me/submissions/3f9e7b73-1cf9-4b8b-adc5-23deffa30d3d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulProfitNPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (cash extra discount : ℕ → ℝ) (n : ℕ) : ulProfitNPV (fun t => cash t+extra t) discount n=ulProfitNPV cash discount n+ulProfitNPV extra discount n := by
  unfold ulProfitNPV
  simp only [ulDiscountedProfit, add_mul, Finset.sum_add_distrib]
