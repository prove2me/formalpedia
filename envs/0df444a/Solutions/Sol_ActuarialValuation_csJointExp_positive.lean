-- Prove2me | solution 1 for ActuarialValuation.csJointExp_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:07:21.264102+00:00
-- url     : https://prove2.me/submissions/c4015ebe-1707-4154-916b-23ef6b677c47

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csJointExp
open ActuarialValuation

theorem solution(a b c s t : ℝ) : 0 < csJointExp a b c s t := by
  unfold csJointExp
  exact Real.exp_pos _
