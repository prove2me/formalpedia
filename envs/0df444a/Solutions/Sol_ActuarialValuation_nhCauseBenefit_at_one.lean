-- Prove2me | solution 1 for ActuarialValuation.nhCauseBenefit_at_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:05:12.176087+00:00
-- url     : https://prove2.me/submissions/43fe2f46-f0f2-4910-95b0-1ace71e83f90

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhCauseBenefit
open ActuarialValuation

theorem solution(B1 B2 : ℝ) : nhCauseBenefit 1 B1 B2=B1 := by
  simp [nhCauseBenefit]
