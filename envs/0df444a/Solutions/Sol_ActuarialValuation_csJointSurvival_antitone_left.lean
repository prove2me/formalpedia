-- Prove2me | solution 1 for ActuarialValuation.csJointSurvival_antitone_left
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:21:31.557987+00:00
-- url     : https://prove2.me/submissions/822b459f-42f3-4681-8966-3144fccabfe5

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
    (s1 s2 t : ℝ) (h : s1 ≤ s2) :
    csJointSurvival μ U V Z s2 t ≤ csJointSurvival μ U V Z s1 t := by
  unfold csJointSurvival
  apply measure_mono
  intro ω hω
  exact ⟨by linarith [hω.1], hω.2⟩
