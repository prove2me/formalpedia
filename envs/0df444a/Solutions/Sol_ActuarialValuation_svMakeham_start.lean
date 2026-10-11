-- Prove2me | solution 1 for ActuarialValuation.svMakeham_start
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:11:25.385511+00:00
-- url     : https://prove2.me/submissions/62cff1ae-e786-4223-ad4f-3544ca80bc8b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svMakehamCumulativeHazard
open ActuarialValuation

theorem solution(a b c : ℝ) : svMakehamCumulativeHazard a b c 0 = 0 := by
  simp [svMakehamCumulativeHazard, svGompertzCumulativeHazard]
