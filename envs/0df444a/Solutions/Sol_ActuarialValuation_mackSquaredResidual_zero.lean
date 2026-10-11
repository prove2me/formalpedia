-- Prove2me | solution 1 for ActuarialValuation.mackSquaredResidual_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:14:41.103852+00:00
-- url     : https://prove2.me/submissions/395dd01f-c2e5-4c5a-8cd4-d72a8297a5b3

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackSquaredResidual
open ActuarialValuation

theorem solution(actual : ℝ) : mackSquaredResidual actual actual = 0 := by
  simp [mackSquaredResidual]
