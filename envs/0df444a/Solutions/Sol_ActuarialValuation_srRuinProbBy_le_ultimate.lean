-- Prove2me | solution 1 for ActuarialValuation.srRuinProbBy_le_ultimate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:26:32.161975+00:00
-- url     : https://prove2.me/submissions/90716a7c-7cc9-44ff-8a1a-ba008405ab8f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srRuinProbability
import Definitions.Def_actuarial_srRuinProbabilityBy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] (u c : ℝ) (W Y : ℕ → Ω → ℝ) (N : ℕ) : srRuinProbabilityBy μ u c W Y N≤srRuinProbability μ u c W Y := by
  have hsub : {ω | srRuinBy u c W Y N ω} ⊆
      {ω | srEverRuin u c W Y ω} := by
    intro ω hby
    rcases hby with ⟨n, hnN, hn⟩
    exact ⟨n, hn⟩
  have hmeasure : μ {ω | srRuinBy u c W Y N ω} ≤
      μ {ω | srEverRuin u c W Y ω} := MeasureTheory.measure_mono hsub
  have hbound : μ {ω | srEverRuin u c W Y ω} ≤ 1 := by
    calc
      μ {ω | srEverRuin u c W Y ω} ≤ μ Set.univ :=
        MeasureTheory.measure_mono (Set.subset_univ _)
      _ = 1 := MeasureTheory.measure_univ
  have hfinite : μ {ω | srEverRuin u c W Y ω} ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hbound (by simp))
  unfold srRuinProbabilityBy srRuinProbability
  exact ENNReal.toReal_mono hfinite hmeasure
