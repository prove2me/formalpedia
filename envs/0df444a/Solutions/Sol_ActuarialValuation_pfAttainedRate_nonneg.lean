-- Prove2me | solution 1 for ActuarialValuation.pfAttainedRate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:50:49.595618+00:00
-- url     : https://prove2.me/submissions/b01f128c-0cb7-4220-a700-7dba6e4babc0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfAttainedRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (total past payroll : ℝ) (h : past≤total) (hp : 0<payroll) : 0≤pfAttainedRate total past payroll := by
  unfold pfAttainedRate
  exact div_nonneg (sub_nonneg.mpr h) hp.le
