-- Prove2me | solution 1 for ActuarialValuation.ulDeathBenefit_equal_fund
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:20:38.351827+00:00
-- url     : https://prove2.me/submissions/f02c527e-28b6-4236-ad63-ee2666d38cbe

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulDeathBenefit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (fund guarantee : ℝ) (h : guarantee≤fund) : ulDeathBenefit fund guarantee=fund := by
  unfold ulDeathBenefit
  exact max_eq_left h
