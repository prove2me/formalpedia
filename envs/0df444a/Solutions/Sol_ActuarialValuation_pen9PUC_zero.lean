-- Prove2me | solution 1 for ActuarialValuation.pen9PUC_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:24:03.974659+00:00
-- url     : https://prove2.me/submissions/770f5b4c-8167-42a1-a132-9fb14818d3c9

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9PUC
open ActuarialValuation

theorem solution(a projected f : ℝ) : pen9PUC a projected f 0 = 0 := by
  simp [pen9PUC]
