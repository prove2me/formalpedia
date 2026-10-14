-- Prove2me | solution 1 for ActuarialValuation.svSurvival_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:53:08.906982+00:00
-- url     : https://prove2.me/submissions/d820ef8d-958b-44a3-8bc8-ef5899d491cc

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) (s t : ℝ) (hst : s ≤ t) : svSurvival μ T t ≤ svSurvival μ T s := by
  unfold svSurvival
  apply MeasureTheory.measure_mono
  intro ω hω
  exact lt_of_le_of_lt hst hω
