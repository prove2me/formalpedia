-- Prove2me | solution 1 for ActuarialValuation.csMarginalTwo_start
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:27:37.441159+00:00
-- url     : https://prove2.me/submissions/b39445c4-a32d-45f8-a868-9cd78632539f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csMarginalTwoExp
open ActuarialValuation

theorem solution(b c : ℝ) : csMarginalTwoExp b c 0 = 1 := by
  simp [csMarginalTwoExp]
