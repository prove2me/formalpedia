-- Prove2me | solution 1 for ActuarialValuation.csLifeBeforeIdiosyncratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:56:28.826209+00:00
-- url     : https://prove2.me/submissions/1df10779-5629-4a41-af52-8da5b4680137

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true


theorem solution (U Z : ℝ) : min U Z ≤ U := by
  exact min_le_left U Z
