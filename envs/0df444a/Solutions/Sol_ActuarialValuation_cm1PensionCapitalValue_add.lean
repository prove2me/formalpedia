-- Prove2me | solution 1 for ActuarialValuation.cm1PensionCapitalValue_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:11:28.661497+00:00
-- url     : https://prove2.me/submissions/e9df3f3f-b242-4cc8-bb3e-397e8e836aa3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1PensionCapitalValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p q a : ℝ) :
    cm1PensionCapitalValue (p+q) a =
      cm1PensionCapitalValue p a + cm1PensionCapitalValue q a := by
  simp only [cm1PensionCapitalValue, add_mul]
