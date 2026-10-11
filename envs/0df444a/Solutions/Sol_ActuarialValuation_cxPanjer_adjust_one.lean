-- Prove2me | solution 1 for ActuarialValuation.cxPanjer_adjust_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:26:41.63792+00:00
-- url     : https://prove2.me/submissions/c353f6f3-295e-4a05-b5ce-e793fd45cc8b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPanjerAdjustment
open ActuarialValuation

theorem solution(f0 : ℝ) : cxPanjerAdjustment 0 f0 = 1 := by
  simp [cxPanjerAdjustment]
