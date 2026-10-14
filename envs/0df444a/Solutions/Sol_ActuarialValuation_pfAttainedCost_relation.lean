-- Prove2me | solution 1 for ActuarialValuation.pfAttainedCost_relation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:43:00.070713+00:00
-- url     : https://prove2.me/submissions/a4abffbd-d90e-49d2-8ed0-1d5cc6afefd1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfAttainedRate
import Definitions.Def_actuarial_pfAttainedNormalCost

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (total past payroll pay : ℝ) : pfAttainedNormalCost total past payroll pay=pfAttainedRate total past payroll*pay := by
  rfl
