-- Prove2me | solution 1 for ActuarialValuation.srRuinProb_monotone_capital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:24:57.604871+00:00
-- url     : https://prove2.me/submissions/7145fb16-7544-417b-9631-eca62a0a7577

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_srRuinProbability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] (u v c : ℝ) (W Y : ℕ → Ω → ℝ) (h : u≤v) : srRuinProbability μ v c W Y≤srRuinProbability μ u c W Y := by
  have hsub : {ω | srEverRuin v c W Y ω} ⊆
      {ω | srEverRuin u c W Y ω} := by
    intro ω hv
    rcases hv with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    change srSurplus v c W Y n ω < 0 at hn
    change srSurplus u c W Y n ω < 0
    unfold srSurplus at hn ⊢
    linarith
  have hmeasure : μ {ω | srEverRuin v c W Y ω} ≤
      μ {ω | srEverRuin u c W Y ω} := MeasureTheory.measure_mono hsub
  have hbound : μ {ω | srEverRuin u c W Y ω} ≤ 1 := by
    calc
      μ {ω | srEverRuin u c W Y ω} ≤ μ Set.univ :=
        MeasureTheory.measure_mono (Set.subset_univ _)
      _ = 1 := MeasureTheory.measure_univ
  have hfinite : μ {ω | srEverRuin u c W Y ω} ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hbound (by simp))
  unfold srRuinProbability
  exact ENNReal.toReal_mono hfinite hmeasure
