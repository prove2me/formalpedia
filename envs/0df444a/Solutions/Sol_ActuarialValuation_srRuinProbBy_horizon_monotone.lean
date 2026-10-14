-- Prove2me | solution 1 for ActuarialValuation.srRuinProbBy_horizon_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:39:49.883806+00:00
-- url     : https://prove2.me/submissions/b07f172d-7e2b-4061-aab9-a17b2dcba025

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srRuinProbabilityBy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] (u c : ℝ) (W Y : ℕ → Ω → ℝ) (N M : ℕ) (h : N≤M) : srRuinProbabilityBy μ u c W Y N≤srRuinProbabilityBy μ u c W Y M := by
  unfold srRuinProbabilityBy
  apply ENNReal.toReal_mono
  · exact MeasureTheory.measure_ne_top μ _
  · apply MeasureTheory.measure_mono
    intro ω hω
    rcases hω with ⟨n, hn, hr⟩
    exact ⟨n, le_trans hn h, hr⟩
