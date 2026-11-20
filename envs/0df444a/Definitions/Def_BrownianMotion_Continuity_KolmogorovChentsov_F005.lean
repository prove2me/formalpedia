-- Prove2me | Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsov_F005
-- name    : BrownianMotion_Continuity_KolmogorovChentsov_F005
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:21:09.396862+00:00
-- url     : https://prove2.me/theorems/f51d02c1-224f-461a-ab0d-0856b7ff4280
-- title:
--   Source declarations: BrownianMotion.Continuity.KolmogorovChentsov
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.Continuity.KolmogorovChentsov. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsov_F001
import Definitions.Def_SourceProof_ceef003ef78e7468e29c22f2

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

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
lemma holderModification_eq (hT : HasBoundedCoveringNumber U c d) (hU : IsOpen U)
    [DecidablePred (· ∈ U)]
    (hX : IsKolmogorovProcess X P p q M) (hβ_pos : 0 < β)
    (t' : denseCountable T) (ht'U : ↑t' ∈ U)
    {ω : Ω} (hω : ω ∈ holderSet X (denseCountable T) p β U) :
    holderModification X β p U t' ω = X t' ω := by
  rw [← edist_eq_zero]
  exact edist_holderModification_eq_zero hT hU hX hβ_pos t' ht'U hω
variable [IsFiniteMeasure P]

lemma modification_holderModification (hT : HasBoundedCoveringNumber U c d)
    [DecidablePred (· ∈ U)] (hU : IsOpen U)
    (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q) (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p)
    (t : T) (htU : t ∈ U) :
    holderModification X β p U t =ᵐ[P] X t := by
  have h := _root_.Prove2MeSourceProof.h_ceef003ef78e7468e29c22f2 hT hU hX hc hd_pos hdq_lt hβ_pos hβ_lt t htU
  filter_upwards [h] with ω hω using edist_eq_zero.1 hω
omit [MeasurableSpace E] [BorelSpace E] [Nonempty E] [CompleteSpace E] in
lemma StronglyMeasurable.measurableSet_eq_of_continuous {f g : T → Ω → E}
    (hf : ∀ ω, Continuous (f · ω)) (hg : ∀ ω, Continuous (g · ω))
    (hf_meas : ∀ t, StronglyMeasurable (f t)) (hg_meas : ∀ t, StronglyMeasurable (g t)) :
    MeasurableSet {ω | ∀ t, f t ω = g t ω} := by
  obtain ⟨T', hT'_countable, hT'_dense⟩ := TopologicalSpace.exists_countable_dense T
  have : {ω | ∀ (t : T), f t ω = g t ω} = {ω | ∀ (t : T'), f t ω = g t ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Subtype.forall]
    refine ⟨fun h t _ ↦ h t, fun h ↦ ?_⟩
    rw [← funext_iff]
    exact Continuous.ext_on hT'_dense (hf ω) (hg ω) h
  rw [this]
  have : {ω | ∀ (t : T'), f t ω = g t ω} = ⋂ (t : T'), {ω | f t ω = g t ω} := by
    ext; simp
  rw [this]
  have : Countable T' := hT'_countable
  refine MeasurableSet.iInter (fun t ↦ ?_)
  exact StronglyMeasurable.measurableSet_eq_fun (hf_meas t) (hg_meas t)
omit [MeasurableSpace E] [BorelSpace E] [Nonempty E] [CompleteSpace E] in
lemma Measurable.measurableSet_eq_of_continuous {f g : T → Ω → E}
    (hf : ∀ ω, Continuous (f · ω)) (hg : ∀ ω, Continuous (g · ω))
    (h_meas : ∀ t, Measurable (fun ω ↦ edist (f t ω) (g t ω))) :
    MeasurableSet {ω | ∀ t, f t ω = g t ω} := by
  obtain ⟨T', hT'_countable, hT'_dense⟩ := TopologicalSpace.exists_countable_dense T
  have : {ω | ∀ (t : T), f t ω = g t ω} = {ω | ∀ (t : T'), f t ω = g t ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Subtype.forall]
    refine ⟨fun h t _ ↦ h t, fun h ↦ ?_⟩
    rw [← funext_iff]
    exact Continuous.ext_on hT'_dense (hf ω) (hg ω) h
  rw [this]
  have : {ω | ∀ (t : T'), f t ω = g t ω} = ⋂ (t : T'), {ω | f t ω = g t ω} := by ext; simp
  rw [this]
  have : Countable T' := hT'_countable
  refine MeasurableSet.iInter (fun t ↦ ?_)
  suffices MeasurableSet {ω | edist (f t ω) (g t ω) = 0} by convert this with ω; simp
  exact StronglyMeasurable.measurableSet_eq_fun (h_meas t).stronglyMeasurable (by fun_prop)
omit hE [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
lemma Measurable.measurableSet_eqOn_of_continuous {f g : T → Ω → E} (hU : IsOpen U)
    (hf : ∀ ω, ContinuousOn (f · ω) U) (hg : ∀ ω, ContinuousOn (g · ω) U)
    (h_meas : ∀ t, Measurable (fun ω ↦ edist (f t ω) (g t ω))) :
    MeasurableSet {ω | ∀ t ∈ U, f t ω = g t ω} := by
  obtain ⟨T', hT'_countable, hT'_dense⟩ := TopologicalSpace.exists_countable_dense T
  have : {ω | ∀ t ∈ U, f t ω = g t ω} = {ω | ∀ (t : T'), ↑t ∈ U → f t ω = g t ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Subtype.forall]
    refine ⟨fun h t _ ↦ h t, fun h ↦ ?_⟩
    have h_eqOn : Set.EqOn (f · ω) (g · ω) (T' ∩ U) := by
      intro t htU
      exact h t htU.1 htU.2
    refine Set.EqOn.of_subset_closure h_eqOn (hf ω) (hg ω) Set.inter_subset_right ?_
    exact subset_closure_dense_inter hT'_dense hU
  rw [this]
  have : {ω | ∀ (t : T'), ↑t ∈ U → f t ω = g t ω}
      = ⋂ (t : T') (ht : ↑t ∈ U), {ω | f t ω = g t ω} := by
    ext; simp
  rw [this]
  have : Countable T' := hT'_countable
  refine MeasurableSet.iInter (fun t ↦ ?_)
  by_cases htU : ↑t ∈ U
  · simp only [htU, Set.iInter_true]
    suffices MeasurableSet {ω | edist (f t ω) (g t ω) = 0} by
      convert this with ω
      simp
    exact StronglyMeasurable.measurableSet_eq_fun (h_meas t).stronglyMeasurable (by fun_prop)
  · simp [htU]
end EMetricSpace

end ProbabilityTheory


