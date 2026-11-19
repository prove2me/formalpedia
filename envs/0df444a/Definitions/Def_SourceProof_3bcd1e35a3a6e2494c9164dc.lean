-- Prove2me | Definitions.Def_SourceProof_3bcd1e35a3a6e2494c9164dc
-- name    : SourceProof_3bcd1e35a3a6e2494c9164dc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:09:47.846191+00:00
-- url     : https://prove2.me/theorems/69039a10-0eec-4880-81bc-4c5e28cab590
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.ae_eq_zero_of_forall_setIntegral_eq_zero_directed
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_SetIntegralPiSystem_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Vanishing set integrals over a π-system

A function that integrates to zero over every set of a π-system integrates to zero over every
set of the σ-algebra that π-system generates, because the sets on which it integrates to zero
form a Dynkin system. If the function is also measurable for that σ-algebra, it vanishes.
-/

open MeasureTheory
open scoped ENNReal

namespace LevyStochCalc.Probability

variable {α : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


theorem _root_.Prove2MeSourceProof.h_3bcd1e35a3a6e2494c9164dc {m m0 : MeasurableSpace α}
    (hm : m ≤ m0) {μ : Measure α} [IsFiniteMeasure μ] {ι : Type*} [Nonempty ι]
    {𝒢 : ι → MeasurableSpace α} (hdir : Directed (· ≤ ·) 𝒢) (hgen : m = ⨆ i, 𝒢 i)
    {f : α → E} (hf : Integrable f μ) (hfm : StronglyMeasurable[m] f)
    (h : ∀ i, ∀ s, MeasurableSet[𝒢 i] s → ∫ x in s, f x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  have hpi : IsPiSystem (⋃ i, {t | MeasurableSet[𝒢 i] t}) := by
    rintro s hs t ht -
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hs ht ⊢
    obtain ⟨i, hi⟩ := hs
    obtain ⟨j, hj⟩ := ht
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, (hik _ hi).inter (hjk _ hj)⟩
  have hgen' : m = MeasurableSpace.generateFrom (⋃ i, {t | MeasurableSet[𝒢 i] t}) := by
    rw [hgen]
    exact (MeasurableSpace.generateFrom_iUnion_measurableSet 𝒢).symm
  have hmem : ∀ s ∈ ⋃ i, {t | MeasurableSet[𝒢 i] t}, ∫ x in s, f x ∂μ = 0 := by
    rintro s hs
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hs
    obtain ⟨i, hi⟩ := hs
    exact h i s hi
  have h_univ : ∫ x, f x ∂μ = 0 := by
    have huniv := hmem Set.univ (by
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨Classical.arbitrary ι, MeasurableSet.univ⟩)
    simpa using huniv
  exact LevyStochCalc.Probability.ae_eq_zero_of_forall_setIntegral_eq_zero_isPiSystem hm hgen' hpi hf hfm h_univ hmem
end LevyStochCalc.Probability


