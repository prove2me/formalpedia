-- Prove2me | solution 1 for ActuarialValuation.nhDeathPV_zero_benefits
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:11:03.508405+00:00
-- url     : https://prove2.me/submissions/1f0f708e-56b6-4ce5-a503-ada8674e1cb3

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhDeathPV
open ActuarialValuation

theorem solution(a b p δ T t : ℝ) : nhDeathPV a b p δ 0 0 T t=0 := by
  simp [nhDeathPV, nhCauseBenefit]
