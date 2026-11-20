-- Prove2me | Definitions.Def_SourceProof_b53022bf4ec47748c83ffa9f
-- name    : SourceProof_b53022bf4ec47748c83ffa9f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T12:53:57.741267+00:00
-- url     : https://prove2.me/theorems/34ff8b58-4893-49cc-8959-413933973abb
-- title:
--   LevyStochCalc source module: SourceProof_b53022bf4ec47748c83ffa9f
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.referenceIntensity_inter_time` comes from the `LevyStochCalc.Poisson.Simplicity` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Time-simplicity of a Poisson random measure on a finite-intensity set

On a set of finite reference intensity the count of a Poisson random measure exceeds one with
probability at most the square of the intensity. The reference intensity is a product with
Lebesgue measure in time, so the masses of the dyadic time slabs of such a set are the integrals
of an integrable density over intervals of vanishing length, and therefore have vanishing
supremum. A union bound then makes the probability that some slab of level `n` carries two or
more points tend to zero, so almost surely no two points share a time and every point is simple.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Tail

end Tail

section Mesh

end Mesh

section Simple


theorem _root_.Prove2MeSourceProof.h_b53022bf4ec47748c83ffa9f {B : Set (ℝ × E)} (hB : MeasurableSet B) {S : Set ℝ}
    (hS : MeasurableSet S) :
    referenceIntensity ν (B ∩ S ×ˢ Set.univ) = ∫⁻ x in S, sectionDensity ν B x := by
  have hpre : ∀ x : ℝ, ν (Prod.mk x ⁻¹' (B ∩ S ×ˢ Set.univ))
      = S.indicator (fun y => ν (Prod.mk y ⁻¹' B)) x := by
    intro x
    by_cases hx : x ∈ S
    · have hset : Prod.mk x ⁻¹' (B ∩ S ×ˢ Set.univ) = Prod.mk x ⁻¹' B := by
        ext e; simp [hx]
      rw [hset, Set.indicator_of_mem hx]
    · have hset : Prod.mk x ⁻¹' (B ∩ S ×ˢ Set.univ) = (∅ : Set E) := by
        ext e; simp [hx]
      rw [hset, Set.indicator_of_notMem hx, measure_empty]
  rw [LevyStochCalc.Poisson.referenceIntensity, Measure.prod_apply (hB.inter (hS.prod MeasurableSet.univ))]
  simp_rw [hpre]
  rw [lintegral_indicator hS, Measure.restrict_restrict hS]
  simp only [LevyStochCalc.Poisson.sectionDensity]
  rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    Set.inter_comm]
end Simple

end LevyStochCalc.Poisson


