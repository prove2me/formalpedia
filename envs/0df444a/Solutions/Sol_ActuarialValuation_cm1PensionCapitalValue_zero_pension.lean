-- Prove2me | solution 1 for ActuarialValuation.cm1PensionCapitalValue_zero_pension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:33:30.437328+00:00
-- url     : https://prove2.me/submissions/8cee1ddd-7bee-4345-944f-9f3db18b3a62

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1PensionCapitalValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a : ℝ) : cm1PensionCapitalValue 0 a = 0 := by
  simp [cm1PensionCapitalValue]
