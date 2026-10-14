-- Prove2me | solution 1 for ActuarialValuation.ulDiscountedProfit_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:21:01.920994+00:00
-- url     : https://prove2.me/submissions/d33f1829-4d55-425b-bb7f-a6b07aa01436

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulDiscountedProfit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (profit discount : ℝ) (hp : 0≤profit) (hd : 0≤discount) : 0≤ulDiscountedProfit profit discount := by
  unfold ulDiscountedProfit
  exact mul_nonneg hp hd
