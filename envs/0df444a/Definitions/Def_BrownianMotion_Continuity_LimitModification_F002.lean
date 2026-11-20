-- Prove2me | Definitions.Def_BrownianMotion_Continuity_LimitModification_F002
-- name    : BrownianMotion_Continuity_LimitModification_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T07:57:42.814663+00:00
-- url     : https://prove2.me/theorems/f30c4862-55a0-4397-904b-5285270b2ef1
-- title:
--   Source declarations: BrownianMotion.Continuity.LimitModification
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.Continuity.LimitModification. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_LimitModification_F000
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F001

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

lemma measurable_pair_limUnder_comap {T : Type*} [PseudoEMetricSpace T]
    {X₁ X₂ : T → Ω → E} {T' : Set T} (hT'_dense : Dense T')
    (hX₁₂ : ∀ i j, Measurable[_, borel (E × E)] fun ω ↦ (X₁ i ω, X₂ j ω))
    (s t : T)
    (hX₁_tendsto : ∀ ω, ∃ x, Tendsto (fun t' : T' ↦ X₁ t' ω) (comap Subtype.val (𝓝 s)) (𝓝 x))
    (hX₂_tendsto : ∀ ω, ∃ x, Tendsto (fun t' : T' ↦ X₂ t' ω) (comap Subtype.val (𝓝 t)) (𝓝 x)) :
    Measurable[_, borel (E × E)] fun ω ↦
      (limUnder (comap Subtype.val (𝓝 s)) fun t' : T' ↦ X₁ t' ω,
        limUnder (comap Subtype.val (𝓝 t)) fun t' : T' ↦ X₂ t' ω) := by
  have : @NeBot { x // x ∈ T' } (comap Subtype.val (𝓝 s)) := by
    apply IsDenseInducing.comap_nhds_neBot (Dense.isDenseInducing_val hT'_dense)
  have : @NeBot { x // x ∈ T' } (comap Subtype.val (𝓝 t)) := by
    apply IsDenseInducing.comap_nhds_neBot (Dense.isDenseInducing_val hT'_dense)
  let f (x : T' × T') (ω : Ω) := (X₁ x.1 ω, X₂ x.2 ω)
  have hf_tendsto ω : ∃ c,
      Tendsto (f · ω) (comap Subtype.val (𝓝 s) ×ˢ comap Subtype.val (𝓝 t)) (𝓝 c) := by
    obtain ⟨c₀, h₀⟩ := hX₁_tendsto ω
    obtain ⟨c₁, h₁⟩ := hX₂_tendsto ω
    use (c₀, c₁)
    rw [nhds_prod_eq]
    apply Filter.Tendsto.prodMk
    · exact h₀.comp tendsto_fst
    · exact h₁.comp tendsto_snd
  have h_edist_zero ω : edist ((limUnder (comap Subtype.val (𝓝 s)) fun (t' : T') ↦ X₁ t' ω,
        limUnder (comap Subtype.val (𝓝 t)) fun (t' : T') ↦ X₂ t' ω))
      (limUnder ((comap Subtype.val (𝓝 s)) ×ˢ (comap Subtype.val (𝓝 t)))
        fun (p : T' × T') ↦ (X₁ p.1 ω, X₂ p.2 ω)) = 0 := by
    have h := edist_limUnder_prod_eq_zero (hX₁_tendsto ω) (hX₂_tendsto ω)
    rwa [edist_comm] at h
  borelize (E × E)
  refine Measurable.of_edist_eq_zero ?_ h_edist_zero
  exact measurable_limUnder_of_exists_tendsto hf_tendsto (fun i ↦ hX₁₂ i.1 i.2)
lemma measurable_pair_limUnder_indicatorProcess
    {T : Type*} [PseudoEMetricSpace T] [SecondCountableTopology T]
    [MeasurableSpace E] [BorelSpace E]
    {X X' : T → Ω → E}
    (hX : ∀ t, Measurable (X t)) (hX' : ∀ t, Measurable (X' t))
    (hX_pair : ∀ i j, Measurable[_, borel (E × E)] fun ω ↦ (X i ω, X' j ω))
    {A₁ A₂ : Set Ω} (hA₁ : MeasurableSet A₁) (hA₂ : MeasurableSet A₂)
    (s t : T)
    (h_tendsto₁ : ∀ ω ∈ A₁, ∃ c, Tendsto (fun t' : denseCountable T ↦ X t' ω)
      (comap Subtype.val (𝓝 s)) (𝓝 c))
    (h_tendsto₂ : ∀ ω ∈ A₂, ∃ c, Tendsto (fun t' : denseCountable T ↦ X' t' ω)
      (comap Subtype.val (𝓝 t)) (𝓝 c)) :
    Measurable[_, borel (E × E)] fun ω ↦
      (limUnder (comap Subtype.val (𝓝 s)) fun t' : denseCountable T ↦ indicatorProcess X A₁ t' ω,
        limUnder (comap Subtype.val (𝓝 t))
          fun t' : denseCountable T ↦ indicatorProcess X' A₂ t' ω) := by
  refine measurable_pair_limUnder_comap dense_denseCountable ?_ _ _ ?_ ?_
    (X₁ := indicatorProcess X A₁)
  · exact fun i j ↦ measurable_pair_indicatorProcess hX hX' hX_pair hA₁ hA₂ i j
  · intro ω
    by_cases hω : ω ∈ A₁
    · simpa [hω, indicatorProcess] using h_tendsto₁ ω hω
    · simp only [indicatorProcess, hω, ↓reduceIte]
      exact ⟨hE.some, tendsto_const_nhds⟩
  · intro ω
    by_cases hω : ω ∈ A₂
    · simpa [hω, indicatorProcess] using h_tendsto₂ ω hω
    · simp only [indicatorProcess, hω, ↓reduceIte]
      exact ⟨hE.some, tendsto_const_nhds⟩
end ProbabilityTheory


