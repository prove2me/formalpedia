-- Prove2me | Definitions.Def_SourceProof_62dfde857e76a0eeed3ee854
-- name    : SourceProof_62dfde857e76a0eeed3ee854
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:32:17.882727+00:00
-- url     : https://prove2.me/theorems/2db12a72-db11-4108-a799-1472571a966c
-- title:
--   LevyStochCalc source module: SourceProof_62dfde857e76a0eeed3ee854
-- statement:
--   The original source theorem `UniformContinuousOn.exists_tendsto` comes from the `BrownianMotion.Continuity.KolmogorovChentsov` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_Topology_F000
import Definitions.Def_BrownianMotion_Auxiliary_Topology_F001
import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsovInequality_F002
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F002
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F003
import Definitions.Def_BrownianMotion_Gaussian_StochasticProcesses_F000

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Kolmogorov-Chentsov theorem

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Asymptotics

section aux

theorem _root_.Prove2MeSourceProof.h_62dfde857e76a0eeed3ee854 {α β : Type*} [UniformSpace α] [FirstCountableTopology α]
    [UniformSpace β] [CompleteSpace β] {s t : Set α} (hs : Dense s) (ht : IsOpen t)
    {f : s → β} (hf : UniformContinuousOn f {x | ↑x ∈ t}) (a : α) (ha : a ∈ t) :
    ∃ c, Tendsto f (comap Subtype.val (𝓝 a)) (𝓝 c) := by
  have (u : ℕ → s) (hu : Tendsto (fun n ↦ (u n : α)) atTop (𝓝 a)) :
      ∃ c, Tendsto (f ∘ u) atTop (𝓝 c) := by
    refine cauchySeq_tendsto_of_complete ?_
    rw [cauchySeq_iff_tendsto]
    rw [UniformContinuousOn] at hf
    change Tendsto ((fun p ↦ (f p.1, f p.2)) ∘ (fun p : ℕ × ℕ ↦ (u p.1, u p.2))) atTop
      (uniformity β)
    refine hf.comp ?_
    rw [tendsto_inf]
    constructor
    · suffices hu_cauchy : CauchySeq u by rwa [cauchySeq_iff_tendsto] at hu_cauchy
      have h_cauchy := hu.cauchySeq
      rw [cauchySeq_iff] at h_cauchy
      rw [cauchySeq_iff, uniformity_subtype]
      simp only [mem_comap, forall_exists_index, and_imp] at h_cauchy ⊢
      intro V s hs hsV
      obtain ⟨N, hN⟩ := h_cauchy s hs
      exact ⟨N, fun k hNk l hNl ↦ hsV (hN k hNk l hNl)⟩
    · rw [tendsto_principal]
      have hut : ∀ᶠ n in atTop, (u n : α) ∈ t := hu.eventually_mem (ht.mem_nhds ha)
      simp only [eventually_atTop, Set.mem_prod, Set.mem_setOf_eq, Prod.forall,
        Prod.exists, Prod.mk_le_mk, and_imp] at hut ⊢
      obtain ⟨N, hN⟩ := hut
      exact ⟨N, N, fun a b hNa hNb ↦ ⟨hN a hNa, hN b hNb⟩⟩
  choose c hc using this
  obtain ⟨u, hu⟩ : ∃ u : ℕ → s, Tendsto (fun n ↦ (u n : α)) atTop (𝓝 a) := by
    have has : a ∈ closure s := by simp [hs.closure_eq]
    rw [mem_closure_iff_seq_limit] at has
    obtain ⟨u, hu_mem, hu⟩ := has
    exact ⟨fun n ↦ ⟨u n, hu_mem n⟩, hu⟩
  refine ⟨c u hu, ?_⟩
  refine tendsto_of_seq_tendsto fun v hv' ↦ ?_
  have hv : Tendsto (fun n ↦ (v n : α)) atTop (𝓝 a) := by rwa [tendsto_comap_iff] at hv'
  refine (hc u hu).congr_uniformity ?_
  change Tendsto ((fun p ↦ (f p.1, f p.2)) ∘ (fun n ↦ (u n, v n))) atTop (uniformity β)
  rw [UniformContinuousOn] at hf
  refine hf.comp ?_
  have hu' : Tendsto u atTop (comap Subtype.val (𝓝 a)) := by rwa [tendsto_comap_iff]
  have hv' : Tendsto v atTop (comap Subtype.val (𝓝 a)) := by rwa [tendsto_comap_iff]
  refine Tendsto.mono_right (hu'.prodMk hv') ?_
  rw [le_inf_iff]
  constructor
  · rw [← Filter.comap_prodMap_prod, ← nhds_prod_eq, uniformity_subtype]
    refine comap_mono ?_
    exact nhds_le_uniformity a
  · simp only [le_principal_iff]
    rw [mem_prod_iff]
    simp_rw [Set.prod_subset_prod_iff]
    simp only [mem_comap]
    refine ⟨Subtype.val ⁻¹' t, ⟨t, ?_, subset_rfl⟩, Subtype.val ⁻¹' t, ⟨t, ?_, subset_rfl⟩, ?_⟩
    · exact ht.mem_nhds ha
    · exact ht.mem_nhds ha
    · grind
end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  {X : T → Ω → E} {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0} {P : Measure Ω}
  {U : Set T}

section PseudoEMetricSpace

variable [PseudoEMetricSpace T] [PseudoEMetricSpace E]

section HolderSet

end HolderSet

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [hE : Nonempty E]
  [SecondCountableTopology T]

variable [IsFiniteMeasure P]

end PseudoEMetricSpace

section EMetricSpace

variable [PseudoEMetricSpace T] [EMetricSpace E] [hE : Nonempty E]

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [SecondCountableTopology T]

variable [IsFiniteMeasure P]

end EMetricSpace

end ProbabilityTheory


