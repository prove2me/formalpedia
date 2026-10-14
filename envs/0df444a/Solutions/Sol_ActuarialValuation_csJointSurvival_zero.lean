-- Prove2me | solution 1 for ActuarialValuation.csJointSurvival_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:28:30.442559+00:00
-- url     : https://prove2.me/submissions/e66359ec-b3b0-40da-a086-f91fd5d73cdc

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csJointSurvival
import Definitions.Def_actuarial_csFirstLife

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ)
    (s t : ℝ) (hs : ∀ ω, csFirstLife U Z ω ≤ s) :
    csJointSurvival μ U V Z s t = 0 := by
  have hempty :
      {ω : Ω | s < csFirstLife U Z ω ∧ t < csSecondLife V Z ω} = ∅ := by
    ext ω
    constructor
    · intro hω
      exact (not_lt_of_ge (hs ω)) hω.1
    · intro hω
      simp at hω
  unfold csJointSurvival
  rw [hempty]
  simp
