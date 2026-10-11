-- Prove2me | solution 1 for ActuarialValuation.ruPremiumTotal_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:27:25.417501+00:00
-- url     : https://prove2.me/submissions/5f00fd46-c91e-4635-b9d1-dab9a41237da

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruPremiumTotal
open ActuarialValuation

theorem solution(rate : ℝ) : ruPremiumTotal rate 0 = 0 := by
  simp [ruPremiumTotal]
