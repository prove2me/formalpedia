-- Prove2me | solution 1 for ActuarialValuation.whSquaredResidual_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:34:09.550186+00:00
-- url     : https://prove2.me/submissions/b983ebed-15da-4833-8cfb-8133a3686b10

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whSquaredResidual
open ActuarialValuation

theorem solution(x : ℝ) : whSquaredResidual x x = 0 := by
  simp [whSquaredResidual, whRateResidual]
