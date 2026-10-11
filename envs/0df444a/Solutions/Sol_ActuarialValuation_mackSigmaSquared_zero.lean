-- Prove2me | solution 1 for ActuarialValuation.mackSigmaSquared_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:31:37.521074+00:00
-- url     : https://prove2.me/submissions/f91d31d5-9674-4fb7-b911-0aa7a4ca20f6

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackSigmaSquared
open ActuarialValuation

theorem solution(df : ℝ) : mackSigmaSquared 0 df = 0 := by
  simp [mackSigmaSquared]
