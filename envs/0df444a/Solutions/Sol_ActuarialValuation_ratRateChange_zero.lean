-- Prove2me | solution 1 for ActuarialValuation.ratRateChange_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:43:57.804884+00:00
-- url     : https://prove2.me/submissions/6754d1fb-6aac-435d-80c9-1092ab15f200

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratRateChange
open ActuarialValuation

theorem solution(rate : ℝ) (h : rate ≠ 0) : ratRateChange rate rate = 0 := by
  simp [ratRateChange, h]
