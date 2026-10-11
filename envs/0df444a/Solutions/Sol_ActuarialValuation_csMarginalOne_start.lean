-- Prove2me | solution 1 for ActuarialValuation.csMarginalOne_start
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:29:54.999588+00:00
-- url     : https://prove2.me/submissions/ed6386e9-dff3-40f1-af36-6e1f77a485ce

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csMarginalOneExp
open ActuarialValuation

theorem solution(a c : ℝ) : csMarginalOneExp a c 0 = 1 := by
  simp [csMarginalOneExp]
