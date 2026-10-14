-- Prove2me | solution 1 for ActuarialValuation.ulDeathBenefit_ge_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:21:13.829989+00:00
-- url     : https://prove2.me/submissions/54197801-6540-4938-b4d7-3281d24e6721

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulDeathBenefit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (fund guarantee : ℝ) : guarantee≤ulDeathBenefit fund guarantee := by
  unfold ulDeathBenefit
  exact le_max_right fund guarantee
