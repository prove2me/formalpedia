-- Prove2me | solution 1 for ActuarialValuation.csShock_observed_tie
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:58:00.730651+00:00
-- url     : https://prove2.me/submissions/dff97dec-4f68-464f-8716-65b1bb2c5154

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csFirstLife
import Definitions.Def_actuarial_csSecondLife

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ) (ω : Ω)
    (hzu : Z ω < U ω) (hzv : Z ω < V ω) :
    csFirstLife U Z ω = csSecondLife V Z ω := by
  simp [csFirstLife, csSecondLife,
    min_eq_right (le_of_lt hzu), min_eq_right (le_of_lt hzv)]
