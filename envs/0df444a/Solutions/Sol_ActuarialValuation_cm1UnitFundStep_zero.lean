-- Prove2me | solution 1 for ActuarialValuation.cm1UnitFundStep_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:26:24.178324+00:00
-- url     : https://prove2.me/submissions/b599faee-bcdf-4eb2-9583-11efcc140a58

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1UnitFundStep

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (U P C : ℝ) : cm1UnitFundStep U P C 0 = U + P - C := by
  simp [cm1UnitFundStep]
