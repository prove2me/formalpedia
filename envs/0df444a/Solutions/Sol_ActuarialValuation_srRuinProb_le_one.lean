-- Prove2me | solution 1 for ActuarialValuation.srRuinProb_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:53:35.395328+00:00
-- url     : https://prove2.me/submissions/7deea95a-435a-415c-a7e5-e996b913258b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srRuinProbability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] (u c : ℝ) (W Y : ℕ → Ω → ℝ) : srRuinProbability μ u c W Y≤1 := by
  unfold srRuinProbability
  have hμ : μ {ω | srEverRuin u c W Y ω} ≤ 1 := by
    calc
      μ {ω | srEverRuin u c W Y ω} ≤ μ Set.univ :=
        MeasureTheory.measure_mono (Set.subset_univ _)
      _ = 1 := MeasureTheory.measure_univ
  exact (ENNReal.toReal_mono (by simp) hμ)
  -- Replace the marker above with a complete proof before lint-submit.
