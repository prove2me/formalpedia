-- Prove2me | solution 1 for ActuarialValuation.nhTransition_absorb_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:01:56.672259+00:00
-- url     : https://prove2.me/submissions/b24ff9d9-b5ef-4875-a7de-53a1e8e37dd8

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhTransition
open ActuarialValuation

theorem solution(a b p s t : ℝ) : nhTransition a b p s t 1 1=1 := by
  simp [nhTransition]
