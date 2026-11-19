-- Prove2me | Definitions.Def_BrownianMotion_StochasticIntegral_Cadlag_F001
-- name    : BrownianMotion_StochasticIntegral_Cadlag_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:14:09.966283+00:00
-- url     : https://prove2.me/theorems/e09e5ca8-0e73-4f34-96f8-8b80af3e7fc8
-- title:
--   Source declarations: BrownianMotion.StochasticIntegral.Cadlag
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.StochasticIntegral.Cadlag. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_StochasticIntegral_Cadlag_F000
import Definitions.Def_SourceProof_4d38a48af0fc0a7e05260d81

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-! # cadlag functions

-/

@[expose] public section

open Filter TopologicalSpace Bornology
open scoped Topology ENNReal

variable {ι E : Type*} [TopologicalSpace ι]

section Jump

/-- If `ι` is a compact space, then a càdlàg function has only finitely many large jumps. -/
theorem IsCadlag.finite_largeLeftJumpSet [LinearOrder ι] [OrderTopology ι] [CompactSpace ι]
    [UniformSpace E] {f : ι → E} (hf : IsCadlag f) {v : Set (E × E)} (hv : v ∈ uniformity E) :
    (largeLeftJumpSet f v).Finite := by
  by_contra!
  grind [this.exists_accPt_principal, (_root_.Prove2MeSourceProof.h_4d38a48af0fc0a7e05260d81 hf) hv]
end Jump

@[to_additive (attr := to_fun)]
lemma IsCadlag.mul {E : Type*} [Mul E] [TopologicalSpace E] [ContinuousMul E] [Preorder ι]
    {f g : ι → E} (hf : IsCadlag f) (hg : IsCadlag g) :
    IsCadlag (f * g) := by
  refine ⟨fun i ↦ ContinuousWithinAt.mul (hf.1 i) (hg.1 i), fun i ↦ ?_⟩
  obtain ⟨l, hl⟩ := hf.2 i
  obtain ⟨m, hm⟩ := hg.2 i
  exact ⟨l * m, hl.mul hm⟩
@[to_fun]
lemma IsCadlag.const_smul {E : Type*} [SMul ℝ E] [TopologicalSpace E] [ContinuousSMul ℝ E]
    [Preorder ι] {f : ι → E} (hf : IsCadlag f) (r : ℝ) :
    IsCadlag (r • f) := by
  refine ⟨fun i ↦ ContinuousWithinAt.const_smul (hf.1 i) r, fun i ↦ ?_⟩
  obtain ⟨l, hl⟩ := hf.2 i
  exact ⟨r • l, hl.const_smul r⟩
@[to_additive (attr := to_fun)]
lemma IsCadlag.inv {E : Type*} [Group E] [TopologicalSpace E] [ContinuousInv E] [Preorder ι]
    {f : ι → E} (hf : IsCadlag f) :
    IsCadlag (f⁻¹) := by
  refine ⟨fun i ↦ ContinuousWithinAt.inv (hf.1 i), fun i ↦ ?_⟩
  obtain ⟨l, hl⟩ := hf.2 i
  exact ⟨l⁻¹, hl.inv⟩
@[to_fun]
lemma IsCadlag.sub {E : Type*} [Sub E] [TopologicalSpace E] [ContinuousSub E]
    [Preorder ι] {f g : ι → E} (hf : IsCadlag f) (hg : IsCadlag g) :
    IsCadlag (f - g) := by
  refine ⟨fun i ↦ ContinuousWithinAt.sub (hf.1 i) (hg.1 i), fun i ↦ ?_⟩
  obtain ⟨l, hl⟩ := hf.2 i
  obtain ⟨m, hm⟩ := hg.2 i
  exact ⟨l - m, hl.sub hm⟩
lemma IsCadlag.continuous_comp {κ E F : Type*} [TopologicalSpace κ] [TopologicalSpace E]
    [TopologicalSpace F] [Preorder κ] {g : E → F} {f : κ → E}
    (hg : Continuous g) (hf : IsCadlag f) : IsCadlag (g ∘ f) where
  right_continuous := Function.IsRightContinuous.continuous_comp hg hf.right_continuous
  left_limit i := by
    obtain ⟨l, hl⟩ := hf.left_limit i
    exact ⟨g l, (hg.tendsto l).comp hl⟩
lemma IsCadlag.norm {κ F : Type*} [TopologicalSpace κ] [NormedAddCommGroup F] [Preorder κ]
    {f : κ → F} (hf : IsCadlag f) : IsCadlag (fun i ↦ ‖f i‖) :=
  hf.continuous_comp continuous_norm
lemma IsCadlag.norm_sq {κ F : Type*} [TopologicalSpace κ] [NormedAddCommGroup F] [Preorder κ]
    {f : κ → F} (hf : IsCadlag f) : IsCadlag (fun i ↦ ‖f i‖ ^ 2) :=
  hf.norm.continuous_comp (continuous_pow 2)
/-- A càdlàg function is locally bounded. -/
lemma isLocallyBounded_of_isCadlag {E : Type*} [LinearOrder ι] [PseudoMetricSpace E]
    {f : ι → E} (hf : IsCadlag f) (x : ι) : ∃ t ∈ 𝓝 x, IsBounded (f '' t) := by
  obtain ⟨l, hl⟩ := hf.2 x
  obtain ⟨U, ⟨⟨A, ⟨hp, ⟨W, hW⟩⟩⟩, hU⟩⟩ := Metric.exists_isBounded_image_of_tendsto hl
  obtain ⟨V, ⟨⟨B, ⟨hq, ⟨R, hR⟩⟩⟩, hV⟩⟩ := Metric.exists_isBounded_image_of_tendsto (hf.1 x).tendsto
  refine ⟨A ∩ B, inter_mem hp hq, ?_⟩
  apply IsBounded.subset ((hU.union hV).union (isBounded_singleton : Bornology.IsBounded ({f x})))
  rintro _ ⟨y, ⟨hyL, hyR⟩ , rfl⟩
  rcases lt_trichotomy y x with (hlt | heq | hgt)
  · have : y ∈ U := hW.2 ▸ ⟨hyL, hW.1 hlt⟩
    grind
  · grind
  · have : y ∈ V := hR.2 ▸ ⟨hyR, hR.1 hgt⟩
    grind
/-- A càdlàg function maps compact sets to bounded sets. -/
lemma isBounded_image_of_isCadlag_of_isCompact {E : Type*} [LinearOrder ι] [PseudoMetricSpace E]
    {f : ι → E} (hf : IsCadlag f) {s : Set ι} (hs : IsCompact s) :
    IsBounded (f '' s) :=
  isBounded_image_of_isLocallyBounded_of_isCompact hs (isLocallyBounded_of_isCadlag hf)


