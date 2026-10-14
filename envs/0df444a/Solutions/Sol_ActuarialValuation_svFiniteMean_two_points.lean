-- Prove2me | solution 1 for ActuarialValuation.svFiniteMean_two_points
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:55:26.860573+00:00
-- url     : https://prove2.me/submissions/7e465b1a-a84c-4d51-b398-43b633a425f6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svFiniteMassMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) : svFiniteMassMean p 1 = p 1 := by
  simp [svFiniteMassMean, Finset.sum_range_succ]
