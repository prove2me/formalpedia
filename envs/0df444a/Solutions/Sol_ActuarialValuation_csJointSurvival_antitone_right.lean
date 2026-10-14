-- Prove2me | solution 1 for ActuarialValuation.csJointSurvival_antitone_right
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:22:25.111926+00:00
-- url     : https://prove2.me/submissions/85f3ebb6-1c35-4d02-8f99-2d8775427060

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_csJointSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ)
    (s t1 t2 : ℝ) (h : t1 ≤ t2) :
    csJointSurvival μ U V Z s t2 ≤ csJointSurvival μ U V Z s t1 := by
  unfold csJointSurvival
  apply measure_mono
  intro ω hω
  exact ⟨hω.1, by linarith [hω.2]⟩
