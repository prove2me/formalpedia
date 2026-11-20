-- Prove2me | Definitions.Def_SourceProof_98b1bfd1eba405ec69e0ef6d
-- name    : SourceProof_98b1bfd1eba405ec69e0ef6d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T22:38:22.835071+00:00
-- url     : https://prove2.me/theorems/a614b7de-b76b-47ce-8c50-1adec1ac784e
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indicator_Icc
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLinear_F001
import Definitions.Def_LevyStochCalc_Probability_Progressive_F000

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


theorem _root_.Prove2MeSourceProof.h_98b1bfd1eba405ec69e0ef6d {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {H : Ω → ℝ → ℝ} (hp : Probability.ProgressivelyMeasurable ℱ H) (T : ℝ) :
    Probability.ProgressivelyMeasurable ℱ
      fun ω s => Set.indicator (Set.Icc (0 : ℝ) T) (H ω) s := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator
        (fun s => Set.indicator (Set.Icc (0 : ℝ) T) (H p.1) s) p.2)
      = Set.indicator ((fun p : Ω × ℝ => p.2) ⁻¹' Set.Icc (0 : ℝ) T)
        (fun p : Ω × ℝ => (Set.Iic t).indicator (H p.1) p.2) := by
    funext p
    by_cases h2 : p.2 ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem (Set.mem_preimage.mpr h2)]
      by_cases h1 : p.2 ∈ Set.Iic t
      · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
      · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h1]
    · rw [Set.indicator_of_notMem fun hc => h2 (Set.mem_preimage.mp hc)]
      by_cases h1 : p.2 ∈ Set.Iic t
      · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
      · rw [Set.indicator_of_notMem h1]
  rw [key]
  exact (hp t).indicator (measurable_snd measurableSet_Icc)
section Complete

variable {T : ℝ} {H : ℕ → Ω → ℝ → ℝ}

end Complete

end LevyStochCalc.Brownian.Ito


