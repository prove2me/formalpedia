-- Prove2me | solution 1 for ActuarialValuation.mackScaledResidual_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:42:57.929978+00:00
-- url     : https://prove2.me/submissions/d421947f-95f3-4f7e-82fa-27a319c13e70

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackScaledResidual
open ActuarialValuation

theorem solution(a e : ℝ) : mackScaledResidual a a e = 0 := by
  simp [mackScaledResidual, mackSquaredResidual]
