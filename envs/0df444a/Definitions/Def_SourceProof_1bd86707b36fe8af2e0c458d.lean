-- Prove2me | Definitions.Def_SourceProof_1bd86707b36fe8af2e0c458d
-- name    : SourceProof_1bd86707b36fe8af2e0c458d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T07:58:33.26525+00:00
-- url     : https://prove2.me/theorems/1372d5dd-d0a2-494c-86f6-2597cb57cd88
-- title:
--   LevyStochCalc source proof: ProbabilityTheory.IsLimitOfIndicator.measurable_pair
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_LimitModification_F002

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
#

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section aux

end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : T → Ω → E} {c : ℝ≥0∞}
  {U : Set T}

section IndicatorProcess

variable {A : Set Ω} [hE : Nonempty E]

end IndicatorProcess

variable [PseudoEMetricSpace E] [hE : Nonempty E]
  [TopologicalSpace T] [SecondCountableTopology T]

theorem _root_.Prove2MeSourceProof.h_1bd86707b36fe8af2e0c458d
    {T : Type*} [PseudoEMetricSpace T] [SecondCountableTopology T]
    [MeasurableSpace E] [BorelSpace E]
    {Y X Z X' : T → Ω → E} {U₁ U₂ : Set T}
    (hX : ∀ t, Measurable (X t)) (hX' : ∀ t, Measurable (X' t))
    (hX_pair : ∀ i j, Measurable[_, borel (E × E)] fun ω ↦ (X i ω, X' j ω))
    (hY : IsLimitOfIndicator Y X P U₁) (hZ : IsLimitOfIndicator Z X' P U₂)
    (s t : T) :
    Measurable[_, borel (E × E)] (fun ω ↦ (Y s ω, Z t ω)) := by
  have : @NeBot { x // x ∈ denseCountable T } (comap Subtype.val (𝓝 s)) := by
    apply IsDenseInducing.comap_nhds_neBot (Dense.isDenseInducing_val dense_denseCountable)
  have : @NeBot { x // x ∈ denseCountable T } (comap Subtype.val (𝓝 t)) := by
    apply IsDenseInducing.comap_nhds_neBot (Dense.isDenseInducing_val dense_denseCountable)
  obtain ⟨A₁, hA₁, hA₁_ae, hY_tendsto, hYU, hYUc⟩ := hY
  obtain ⟨A₂, hA₂, hA₂_ae, hZ_tendsto, hZU, hZUc⟩ := hZ
  by_cases hsU₁ : s ∈ U₁ <;> by_cases htU₂ : t ∈ U₂
  · specialize hYU s hsU₁
    specialize hZU t htU₂
    have h_eq ω : edist (Y s ω, Z t ω)
        (dense_denseCountable.extend (fun (t' : denseCountable T) ↦ ProbabilityTheory.indicatorProcess X A₁ t' ω) s,
          dense_denseCountable.extend (fun (t' : denseCountable T) ↦ ProbabilityTheory.indicatorProcess X' A₂ t' ω) t)
        = 0 := by
      simpa [Prod.edist_eq] using ⟨hYU ω, hZU ω⟩
    borelize (E × E)
    refine Measurable.of_edist_eq_zero ?_ h_eq
    simp only [Dense.extend, IsDenseInducing.extend]
    exact ProbabilityTheory.measurable_pair_limUnder_indicatorProcess hX hX' hX_pair hA₁ hA₂ s t (hY_tendsto s hsU₁)
      (hZ_tendsto t htU₂)
  · specialize hYU s hsU₁
    specialize hZUc t htU₂
    have h_eq ω : edist (Y s ω, Z t ω)
        (dense_denseCountable.extend (fun (t' : denseCountable T) ↦ ProbabilityTheory.indicatorProcess X A₁ t' ω) s,
          hE.some)
        = 0 := by
      simpa [Prod.edist_eq] using ⟨hYU ω, hZUc ω⟩
    borelize (E × E)
    refine Measurable.of_edist_eq_zero ?_ h_eq
    suffices Measurable[_, borel (E × E)] fun ω ↦
        (limUnder (comap Subtype.val (𝓝 s)) fun t' : denseCountable T ↦ ProbabilityTheory.indicatorProcess X A₁ t' ω,
        limUnder (comap Subtype.val (𝓝 t))
          fun t' : denseCountable T ↦ ProbabilityTheory.indicatorProcess X' ∅ t' ω) by
      simp only [ProbabilityTheory.indicatorProcess_apply, Set.mem_empty_iff_false, ↓reduceIte] at this
      refine this.of_edist_eq_zero fun ω ↦ ?_
      rw [Prod.edist_eq]
      simp only [max_eq_zero]
      rw [edist_comm hE.some, edist_limUnder_const]
      simp only [and_true]
      exact edist_self _
    exact ProbabilityTheory.measurable_pair_limUnder_indicatorProcess hX hX' hX_pair hA₁ MeasurableSet.empty s t
      (hY_tendsto s hsU₁) (by simp)
  · specialize hYUc s hsU₁
    specialize hZU t htU₂
    have h_eq ω : edist (Y s ω, Z t ω) (hE.some,
        dense_denseCountable.extend (fun (t' : denseCountable T) ↦ ProbabilityTheory.indicatorProcess X' A₂ t' ω) t)
        = 0 := by
      simpa [Prod.edist_eq] using ⟨hYUc ω, hZU ω⟩
    borelize (E × E)
    refine Measurable.of_edist_eq_zero ?_ h_eq
    suffices Measurable[_, borel (E × E)] fun ω ↦
        (limUnder (comap Subtype.val (𝓝 s)) fun t' : denseCountable T ↦ ProbabilityTheory.indicatorProcess X ∅ t' ω,
        limUnder (comap Subtype.val (𝓝 t))
          fun t' : denseCountable T ↦ ProbabilityTheory.indicatorProcess X' A₂ t' ω) by
      simp only [ProbabilityTheory.indicatorProcess_apply, Set.mem_empty_iff_false, ↓reduceIte] at this
      refine this.of_edist_eq_zero fun ω ↦ ?_
      rw [Prod.edist_eq]
      simp only [max_eq_zero]
      rw [edist_comm hE.some, edist_limUnder_const]
      simp only [true_and]
      exact edist_self _
    exact ProbabilityTheory.measurable_pair_limUnder_indicatorProcess hX hX' hX_pair MeasurableSet.empty hA₂ s t
      (by simp) (hZ_tendsto t htU₂)
  · borelize (E × E)
    refine Measurable.of_edist_eq_zero (measurable_const : Measurable fun ω ↦ (hE.some, hE.some)) ?_
    intro ω
    simpa [Prod.edist_eq] using ⟨hYUc s hsU₁ ω, hZUc t htU₂ ω⟩
end ProbabilityTheory


