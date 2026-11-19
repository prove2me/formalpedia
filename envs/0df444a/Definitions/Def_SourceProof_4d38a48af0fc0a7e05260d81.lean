-- Prove2me | Definitions.Def_SourceProof_4d38a48af0fc0a7e05260d81
-- name    : SourceProof_4d38a48af0fc0a7e05260d81
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:09:46.497626+00:00
-- url     : https://prove2.me/theorems/9b659477-6c85-44bb-ad61-78b3512895ed
-- title:
--   LevyStochCalc source proof: IsCadlag.not_accPt_largeLeftJumpSet
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_StochasticIntegral_Cadlag_F000

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


theorem _root_.Prove2MeSourceProof.h_4d38a48af0fc0a7e05260d81 [LinearOrder ι] [OrderTopology ι] [UniformSpace E]
    {f : ι → E} (hf : IsCadlag f) {v : Set (E × E)} (hv : v ∈ uniformity E) (t : ι) :
    ¬ AccPt t (𝓟 (largeLeftJumpSet f v)) := by
  obtain ⟨u, hu, husymm, huv⟩ := comp_comp_symm_mem_uniformity_sets hv
  intro ht
  have hsplit :
    (𝓝[<] t ⊓ 𝓟 (largeLeftJumpSet f v)).NeBot ∨ (𝓝[>] t ⊓ 𝓟 (largeLeftJumpSet f v)).NeBot := by
    simp_all [AccPt, ← nhdsLT_sup_nhdsGT t, inf_comm, inf_sup_left]
  refine hsplit.elim (fun h => ?_) (fun h => ?_)
  · have hnb : (𝓝[<] t).NeBot := h.mono inf_le_left
    rw [← frequently_mem_iff_neBot] at h
    contrapose! h
    have htt : ¬ IsBot t := by
      by_contra
      exact (not_neBot.2 <| nhdsLT_eq_bot_iff.2 (Or.inl this)) hnb
    obtain ⟨a, ha⟩ : ∃ a, a < t := by simpa [IsBot] using htt
    -- There exists `b < t` such that for any `x ∈ Ioo b t`, `f x` is close to `f.leftLim t`.
    obtain ⟨b, hb⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' ha).1 <| (Uniform.tendsto_nhds_left.1
      <| (tendsto_leftLim_of_tendsto (hf.left_limit t))).eventually_mem hu
    -- For any `x ∈ Ioo b t`, there exists `s ∈ Ioc b x` such that `f s` is closed `f.leftLim x`.
    have h2 (x) (hx : x ∈ Set.Ioo b t) : ∃ s, s ∈ Set.Ioc b x ∧ (f s, f.leftLim x) ∈ u := by
      by_cases! hn : (𝓝[<] x).NeBot
      · exact ((eventually_mem_set.2 (Ioc_mem_nhdsLT hx.1)).and <|
          (Uniform.tendsto_nhds_left.1 (tendsto_leftLim_of_tendsto
          (hf.left_limit x))).eventually_mem hu).exists
      · rw [leftLim_eq_of_eq_bot f hn]
        exact ⟨x, ⟨hx.1, refl x⟩, refl_mem_uniformity hu⟩
    refine eventually_of_mem (Ioo_mem_nhdsLT hb.1) fun x hx => ?_
    obtain ⟨s, hs⟩ := h2 x hx
    -- `(f x, f.leftLim t) ∈ u` and `(f s, f.leftLim t) ∈ u` imply that `(f x, s) ∈ u ∘ u`, which
    -- can be used with `(f s, f.leftLim x) ∈ u` to imply that `(f x, f.leftLim x) ∈ u ∘ u ∘ u`.
    simpa [largeLeftJumpSet] using huv <| SetRel.prodMk_mem_comp
      (SetRel.prodMk_mem_comp (hb.2 hx) (SetRel.symm _ (hb.2 ⟨hs.1.1, hs.1.2.trans_lt hx.2⟩))) hs.2
  · -- We use a similar argument to prove this part.
    have hnb : (𝓝[>] t).NeBot := h.mono inf_le_left
    rw [← frequently_mem_iff_neBot] at h
    contrapose! h
    have htt : ¬ IsTop t := by
      by_contra
      exact (not_neBot.2 <| nhdsGT_eq_bot_iff.2 (Or.inl this)) hnb
    obtain ⟨a, ha⟩ : ∃ a, t < a := by simpa [IsTop] using htt
    -- Here one can also use the existence of a right limit instead of right continuity, so this
    -- theorem should also be true for functions with both left and right limits at each point.
    obtain ⟨b, hb⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' ha).1 <|
      (Uniform.continuousWithinAt_iff'_left.1 <| hf.right_continuous t).eventually_mem hu
    have h2 (x) (hx : x ∈ Set.Ioo t b) : ∃ s, s ∈ Set.Ioc t x ∧ (f s, f.leftLim x) ∈ u := by
      by_cases! hn : (𝓝[<] x).NeBot
      · exact ((eventually_mem_set.2 (Ioc_mem_nhdsLT hx.1)).and <| (Uniform.tendsto_nhds_left.1
          (tendsto_leftLim_of_tendsto (hf.left_limit x))).eventually_mem hu).exists
      · rw [leftLim_eq_of_eq_bot f hn]
        exact ⟨x, ⟨hx.1, refl x⟩, refl_mem_uniformity hu⟩
    refine eventually_of_mem (Ioo_mem_nhdsGT hb.1) fun x hx => ?_
    obtain ⟨s, hs⟩ := h2 x hx
    simpa [largeLeftJumpSet] using huv <| SetRel.prodMk_mem_comp
      (SetRel.prodMk_mem_comp (hb.2 hx) (SetRel.symm _ (hb.2 ⟨hs.1.1, hs.1.2.trans_lt hx.2⟩))) hs.2
end Jump


