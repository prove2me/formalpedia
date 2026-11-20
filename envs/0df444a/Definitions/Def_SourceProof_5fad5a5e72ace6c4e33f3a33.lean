-- Prove2me | Definitions.Def_SourceProof_5fad5a5e72ace6c4e33f3a33
-- name    : SourceProof_5fad5a5e72ace6c4e33f3a33
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T22:36:18.053999+00:00
-- url     : https://prove2.me/theorems/ed7cc9ce-800a-409e-84b0-070cbf030607
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Poisson.Compensated.markedEnergy_le_of_vanishing
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedIntegrandComplete_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Completeness of the marked integrands

The marked energy of an integrand over a horizon is the square of its `L²`-seminorm for the
product of the sample measure, Lebesgue measure on the horizon and the mark measure. That space is
complete, so an energy-Cauchy sequence of admissible marked integrands has a limit; a pointwise
`limsup` along an almost-everywhere convergent subsequence provides a genuinely progressively
measurable representative of it.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

omit [IsProbabilityMeasure P] [SigmaFinite ν] in

theorem _root_.Prove2MeSourceProof.h_5fad5a5e72ace6c4e33f3a33 {φ : Ω → ℝ → E → ℝ} {T : ℝ}
    (hz : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → φ ω s e = 0) (T' : ℝ) :
    markedEnergy P ν T' φ ≤ markedEnergy P ν T φ := by
  refine lintegral_mono fun ω => ?_
  have hind : (fun s => ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
      = Set.indicator (Set.Icc (0 : ℝ) T) (fun s => ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) := by
    funext s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs]
      have hzero : (fun e => (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2) = fun _ => (0 : ℝ≥0∞) := by
        funext e; rw [hz ω s e hs]; simp
      rw [hzero]
      simp
  calc ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume
      = ∫⁻ s in Set.Icc (0 : ℝ) T ∩ Set.Icc (0 : ℝ) T',
          ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume := by
        conv_lhs => rw [hind]
        rw [lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
    _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume :=
        lintegral_mono' (Measure.restrict_mono Set.inter_subset_left le_rfl) le_rfl
section Complete

variable {T : ℝ} {φ : ℕ → Ω → ℝ → E → ℝ}

end Complete

end LevyStochCalc.Poisson.Compensated


