-- Prove2me | solution 1 for ActuarialValuation.ulDeathBenefit_ge_fund
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:20:49.076527+00:00
-- url     : https://prove2.me/submissions/656d80c1-a7e9-4313-aadf-74e3b901afa3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulDeathBenefit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (fund guarantee : ℝ) : fund≤ulDeathBenefit fund guarantee := by
  unfold ulDeathBenefit
  exact le_max_left fund guarantee
