-- Prove2me | Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsov_F000
-- name    : BrownianMotion_Continuity_KolmogorovChentsov_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:41:31.73808+00:00
-- url     : https://prove2.me/theorems/cf4ea9e6-e3d8-4bb8-9bce-5ffa7ea96a89
-- title:
--   Source declarations: BrownianMotion.Continuity.KolmogorovChentsov
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.Continuity.KolmogorovChentsov. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
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

lemma UniformContinuous.exists_tendsto {α β : Type*} [UniformSpace α] [FirstCountableTopology α]
    [UniformSpace β] [CompleteSpace β] {s : Set α}
    {f : s → β} (hf : UniformContinuous f) (a : α) (has : a ∈ closure s) :
    ∃ c, Tendsto f (comap Subtype.val (𝓝 a)) (𝓝 c) := by
  have (u : ℕ → s) (hu : Tendsto (fun n ↦ (u n : α)) atTop (𝓝 a)) :
      ∃ c, Tendsto (f ∘ u) atTop (𝓝 c) := by
    refine cauchySeq_tendsto_of_complete ?_
    refine hf.comp_cauchySeq ?_
    have h_cauchy := hu.cauchySeq
    rw [cauchySeq_iff] at h_cauchy
    rw [cauchySeq_iff, uniformity_subtype]
    simp only [mem_comap, ge_iff_le, forall_exists_index, and_imp] at h_cauchy ⊢
    intro V s hs hsV
    obtain ⟨N, hN⟩ := h_cauchy s hs
    exact ⟨N, fun k hNk l hNl ↦ hsV (hN k hNk l hNl)⟩
  choose c hc using this
  obtain ⟨u, hu⟩ : ∃ u : ℕ → s, Tendsto (fun n ↦ (u n : α)) atTop (𝓝 a) := by
    rw [mem_closure_iff_seq_limit] at has
    obtain ⟨u, hu⟩ := has
    exact ⟨fun n ↦ ⟨u n, hu.1 n⟩, hu.2⟩
  refine ⟨c u hu, ?_⟩
  refine tendsto_of_seq_tendsto fun v hv' ↦ ?_
  have hv : Tendsto (fun n ↦ (v n : α)) atTop (𝓝 a) := by rwa [tendsto_comap_iff] at hv'
  refine (hc u hu).congr_uniformity ?_
  change Tendsto ((fun p ↦ (f p.1, f p.2)) ∘ (fun n ↦ (u n, v n))) atTop (uniformity β)
  rw [UniformContinuous] at hf
  refine hf.comp ?_
  have hu' : Tendsto u atTop (comap Subtype.val (𝓝 a)) := by rwa [tendsto_comap_iff]
  have hv' : Tendsto v atTop (comap Subtype.val (𝓝 a)) := by rwa [tendsto_comap_iff]
  refine Tendsto.mono_right (hu'.prodMk hv') ?_
  rw [← Filter.comap_prodMap_prod, ← nhds_prod_eq, uniformity_subtype]
  refine comap_mono ?_
  exact nhds_le_uniformity a
lemma exists_modification_of_edist_modification {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [PseudoEMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {X Y : T → Ω → E} (hY : ∀ t, Measurable (Y t))
    (h_edist : ∀ t, ∀ᵐ ω ∂P, edist (Y t ω) (X t ω) = 0) :
    ∃ Z : T → Ω → E, (∀ t, Measurable (Z t)) ∧ (∀ t ω, edist (Z t ω) (Y t ω) = 0) ∧
      ∀ t, Z t =ᵐ[P] X t := by
  let Z t ω := if ω ∈ {ω | edist (Y t ω) (X t ω) = 0} then X t ω else Y t ω
  have h_edist_Z t ω : edist (Z t ω) (Y t ω) = 0 := by
    simp only [Set.mem_setOf_eq, Z]
    split_ifs with hω
    · rw [edist_comm]
      simp [hω]
    · simp
  have hZ_meas t : Measurable (Z t) := (hY t).of_edist_eq_zero (h_edist_Z t)
  refine ⟨Z, hZ_meas, h_edist_Z, fun t ↦ ?_⟩
  filter_upwards [h_edist t] with ω hω
  simp [Z, hω]
lemma exists_modification_on_of_edist_modification_on {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [PseudoEMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {X Y : T → Ω → E} (hY : ∀ t, Measurable (Y t)) {U : Set T}
    (h_edist : ∀ t ∈ U, ∀ᵐ ω ∂P, edist (Y t ω) (X t ω) = 0) :
    ∃ Z : T → Ω → E, (∀ t, Measurable (Z t)) ∧ (∀ t, ∀ ω, edist (Z t ω) (Y t ω) = 0) ∧
      ∀ t ∈ U, Z t =ᵐ[P] X t := by
  let Z t ω := if ω ∈ {ω | edist (Y t ω) (X t ω) = 0} then X t ω else Y t ω
  have h_edist_Z t ω : edist (Z t ω) (Y t ω) = 0 := by
    simp only [Set.mem_setOf_eq, Z]
    split_ifs with hω
    · rw [edist_comm]
      simp [hω]
    · simp
  have hZ_meas t : Measurable (Z t) := (hY t).of_edist_eq_zero (h_edist_Z t)
  refine ⟨Z, hZ_meas, h_edist_Z, fun t ht ↦ ?_⟩
  filter_upwards [h_edist t ht] with ω hω
  simp [Z, hω]
end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  {X : T → Ω → E} {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0} {P : Measure Ω}
  {U : Set T}

section PseudoEMetricSpace

variable [PseudoEMetricSpace T] [PseudoEMetricSpace E]

lemma _root_.IsCoverWithBoundedCoveringNumber.HasBoundedCoveringNumber_univ
    {C : ℕ → Set T} {c : ℕ → ℝ≥0∞}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d)) (n : ℕ) :
    HasBoundedCoveringNumber (Set.univ : Set (C n)) (c n) d := by
  have h := hC.hasBoundedCoveringNumber n
  refine ⟨?_, fun ε hε ↦ ?_⟩
  · refine lt_of_le_of_lt (le_of_eq ?_) h.ediam_lt_top
    -- missing lemma
    unfold Metric.ediam
    simp [iSup_subtype]
  replace h := h.coveringNumber_le ε (hε.trans_eq ?_)
  swap
  · unfold Metric.ediam
    simp [iSup_subtype]
  refine le_of_eq_of_le ?_ h
  simp only [ENat.toENNReal_inj]
  unfold Metric.coveringNumber
  simp only [Set.subset_univ, iInf_pos]
  classical
  refine le_antisymm ?_ ?_
  · simp only [le_iInf_iff]
    intro A hA hA_cover
    refine (iInf₂_le {x : C n | (x : T) ∈ A} (fun x _ ↦ ?_)).trans ?_
    · have ⟨c, hc_mem, hc_edist⟩ := hA_cover x.2
      exact ⟨⟨c, hA hc_mem⟩, by simpa using hc_mem, hc_edist⟩
    · exact Set.encard_le_encard_of_injOn (f := fun x ↦ (x : T)) (fun _ hx ↦ hx)
        fun x hx y hy hxy ↦ (by ext; exact hxy)
  · simp only [le_iInf_iff]
    intro A hA_cover
    refine (iInf₂_le (A.image (fun x : C n ↦ (x : T))) (by simp)).trans ?_
    refine (iInf_le _ ?_).trans ?_
    · intro x hx_mem
      obtain ⟨c, hc_mem, hc⟩ := hA_cover (Set.mem_univ ⟨x, hx_mem⟩)
      exact ⟨c, by simpa using hc_mem, hc⟩
    · exact Set.encard_image_le _ _
lemma _root_.Measurable.measurableSet_edist_eq_zero_of_continuous [SecondCountableTopology T]
    {f g : T → Ω → E} (hf : ∀ ω, Continuous (f · ω)) (hg : ∀ ω, Continuous (g · ω))
    (h_meas : ∀ t, Measurable (fun ω ↦ edist (f t ω) (g t ω))) :
    MeasurableSet {ω | ∀ t, edist (f t ω) (g t ω) = 0} := by
  obtain ⟨T', hT'_countable, hT'_dense⟩ := TopologicalSpace.exists_countable_dense T
  have : {ω | ∀ (t : T), edist (f t ω) (g t ω) = 0}
      = {ω | ∀ (t : T'), edist (f t ω) (g t ω) = 0} := by
    ext ω
    simp only [Set.mem_setOf_eq, Subtype.forall]
    refine ⟨fun h t _ ↦ h t, fun h ↦ ?_⟩
    rw [← funext_iff]
    exact Continuous.ext_on hT'_dense ((hf ω).edist (hg ω)) (by fun_prop) h
  rw [this]
  have : {ω | ∀ (t : T'), edist (f t ω) (g t ω) = 0}
      = ⋂ (t : T'), {ω | edist (f t ω ) (g t ω) = 0} := by ext; simp
  rw [this]
  have : Countable T' := hT'_countable
  refine MeasurableSet.iInter (fun t ↦ ?_)
  exact StronglyMeasurable.measurableSet_eq_fun (h_meas t).stronglyMeasurable (by fun_prop)
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


