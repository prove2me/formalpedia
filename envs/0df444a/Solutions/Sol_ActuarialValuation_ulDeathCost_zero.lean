-- Prove2me | solution 1 for ActuarialValuation.ulDeathCost_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:59:45.722714+00:00
-- url     : https://prove2.me/submissions/cd65a12e-8f95-4f6b-a969-8a3758cb306b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulDeathCost
open ActuarialValuation

theorem solution(fund guarantee : ℝ) : ulDeathCost 0 fund guarantee=0 := by
  simp [ulDeathCost]
