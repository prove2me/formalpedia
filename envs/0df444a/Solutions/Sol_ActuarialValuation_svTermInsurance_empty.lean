-- Prove2me | solution 1 for ActuarialValuation.svTermInsurance_empty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:55:39.500261+00:00
-- url     : https://prove2.me/submissions/0f36a265-f504-466f-956d-eec4bdab5aef

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svFiniteTermInsurance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p d : ℕ → ℝ) : svFiniteTermInsurance p d 0 = 0 := by
  simp [svFiniteTermInsurance]
