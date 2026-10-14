-- Prove2me | solution 1 for ActuarialValuation.pfAggregateRate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:25:28.818668+00:00
-- url     : https://prove2.me/submissions/ada96e2a-751b-4c36-bc7f-51992c2afa20

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfAggregateRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (benefit assets payroll : ℝ) (h : assets≤benefit) (hp : 0<payroll) : 0≤pfAggregateRate benefit assets payroll := by
  unfold pfAggregateRate
  exact div_nonneg (sub_nonneg.mpr h) hp.le
