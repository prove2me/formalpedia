-- Prove2me | solution 1 for ActuarialValuation.nhCauseBenefit_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:13:21.901362+00:00
-- url     : https://prove2.me/submissions/e88eceb4-d8f7-4203-9d8e-bf780261835f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhCauseBenefit
open ActuarialValuation

theorem solution(B1 B2 : ℝ) : nhCauseBenefit 0 B1 B2=B2 := by
  simp [nhCauseBenefit]
