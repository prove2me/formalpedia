-- Prove2me | solution 1 for ActuarialValuation.nhSurvival_at_zero_hazard
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:25:26.891616+00:00
-- url     : https://prove2.me/submissions/3cb3b3c5-9e13-4595-a220-b681517cbc9f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhSurvival
open ActuarialValuation

theorem solution(s t : ℝ) : nhSurvival 0 0 s t=1 := by
  simp [nhSurvival, nhCumulative]
