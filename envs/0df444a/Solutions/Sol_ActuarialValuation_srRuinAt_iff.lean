-- Prove2me | solution 1 for ActuarialValuation.srRuinAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:18:01.758003+00:00
-- url     : https://prove2.me/submissions/fa4ed2ca-1b25-459a-a9b3-bc4d0ba49f1a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srNetLoss
import Definitions.Def_actuarial_srRuinAt

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} (u c : ℝ) (W Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : srRuinAt u c W Y n ω ↔ u<srNetLoss c W Y n ω := by
  simp only [srRuinAt, srSurplus, sub_lt_zero]
