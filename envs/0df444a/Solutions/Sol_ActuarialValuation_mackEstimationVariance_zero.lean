-- Prove2me | solution 1 for ActuarialValuation.mackEstimationVariance_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:24:09.961693+00:00
-- url     : https://prove2.me/submissions/bf7c7407-d5fc-407a-bb80-618a2f7dce47

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackEstimationVariance
open ActuarialValuation

theorem solution(s d : ℝ) : mackEstimationVariance s 0 d = 0 := by
  simp [mackEstimationVariance]
