-- Prove2me | solution 1 for ActuarialValuation.csLifeBeforeShock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:54:18.797265+00:00
-- url     : https://prove2.me/submissions/2e5866ce-3c6a-4f7a-8409-14de30b8dce2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true


theorem solution (U Z : ℝ) : min U Z ≤ Z := by
  exact min_le_right U Z
