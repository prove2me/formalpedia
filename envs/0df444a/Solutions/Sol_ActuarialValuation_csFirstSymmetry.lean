-- Prove2me | solution 1 for ActuarialValuation.csFirstSymmetry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:56:36.387066+00:00
-- url     : https://prove2.me/submissions/f6de66f5-e5b0-4e69-9be6-ef89d59e86f4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true


theorem solution (U V Z : ℝ) :
    min U (min V Z) = min V (min U Z) := by
  calc
    min U (min V Z) = min (min U V) Z := (min_assoc U V Z).symm
    _ = min (min V U) Z := by rw [min_comm U V]
    _ = min V (min U Z) := min_assoc V U Z
