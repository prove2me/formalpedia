-- Prove2me | Definitions.Def_SourceProof_6afbd3f9a4aa317ea9c9ba3c
-- name    : SourceProof_6afbd3f9a4aa317ea9c9ba3c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T22:37:02.404044+00:00
-- url     : https://prove2.me/theorems/bbcf855b-2d75-4e8f-ad37-625cf2dae5a4
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Brownian.Ito.energy_le_of_vanishing
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIntegrandComplete_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Completeness of the admissible integrands on a horizon

The energy of an integrand over `[0, T]` is the square of its `L²`-seminorm for the product of
the sample measure with Lebesgue measure on the horizon. A sequence of integrands that is Cauchy
for that energy therefore has an `L²`-limit, and the pointwise `limsup` of an almost everywhere
convergent subsequence is a representative of that limit which is again progressively measurable.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_6afbd3f9a4aa317ea9c9ba3c {H : Ω → ℝ → ℝ} {T : ℝ}
    (hz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → H ω s = 0) (T' : ℝ) :
    energy P T' H ≤ energy P T H := by
  refine lintegral_mono fun ω => ?_
  have hind : (fun s => (‖H ω s‖₊ : ℝ≥0∞) ^ 2)
      = Set.indicator (Set.Icc (0 : ℝ) T) (fun s => (‖H ω s‖₊ : ℝ≥0∞) ^ 2) := by
    funext s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs, hz ω s hs]
      simp
  calc ∫⁻ s in Set.Icc (0 : ℝ) T', (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume
      = ∫⁻ s in Set.Icc (0 : ℝ) T ∩ Set.Icc (0 : ℝ) T',
          (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
        conv_lhs => rw [hind]
        rw [lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
    _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
        lintegral_mono' (Measure.restrict_mono Set.inter_subset_left le_rfl) le_rfl
section Complete

variable {T : ℝ} {H : ℕ → Ω → ℝ → ℝ}

end Complete

end LevyStochCalc.Brownian.Ito


