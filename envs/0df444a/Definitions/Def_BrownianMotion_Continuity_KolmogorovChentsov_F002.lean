-- Prove2me | Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsov_F002
-- name    : BrownianMotion_Continuity_KolmogorovChentsov_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:19:01.191969+00:00
-- url     : https://prove2.me/theorems/53dbfe45-8e5a-4cda-b8a3-8121d062450f
-- title:
--   Source declarations: BrownianMotion.Continuity.KolmogorovChentsov
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.Continuity.KolmogorovChentsov. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsov_F000
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

lemma exists_edist_modification_holder_aux' (hT : HasBoundedCoveringNumber U c d)
    (hU : IsOpen U)
    (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t ∈ U, ∀ᵐ ω ∂P, edist (Y t ω) (X t ω) = 0) ∧
      (∀ ω, ∃ C : ℝ≥0, HolderOnWith C β (Y · ω) U) ∧ IsLimitOfIndicator Y X P U := by
  classical
  refine ⟨holderModification X β p U, ?_, ?_, ?_, ?_⟩
  · exact measurable_holderModification hT hU hX hc hd_pos hdq_lt hβ_pos hβ_lt
  · exact _root_.Prove2MeSourceProof.h_ceef003ef78e7468e29c22f2 hT hU hX hc hd_pos hdq_lt hβ_pos hβ_lt
  · exact holderOnWith_holderModification hT hU hX hβ_pos
  · exact isLimitOfIndicator_holderModification hT hU hX hc hd_pos hdq_lt hβ_pos hβ_lt
lemma _root_.HolderOnWith.congr_edist {T E : Type*} [PseudoEMetricSpace T] [PseudoEMetricSpace E]
    {f g : T → E} {U : Set T} {C : ℝ≥0} {β : ℝ≥0}
    (hfg : ∀ s t, s ∈ U → t ∈ U → edist (g s) (g t) = edist (f s) (f t))
    (hf : HolderOnWith C β f U) :
    HolderOnWith C β g U := by
  rw [HolderOnWith] at hf ⊢
  convert hf using 5 with s hsU t htU
  exact hfg s t hsU htU
lemma exists_modification_holder_aux' (hT : HasBoundedCoveringNumber U c d)
    (hU : IsOpen U)
    (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t ∈ U, Y t =ᵐ[P] X t) ∧
      (∀ ω, ∃ C : ℝ≥0, HolderOnWith C β (Y · ω) U) ∧ IsLimitOfIndicator Y X P U := by
  obtain ⟨Y, hY_meas, hY_edist, hY_holder, hY_limit⟩ :=
    exists_edist_modification_holder_aux' hT hU hX hc hd_pos hdq_lt hβ_pos hβ_lt
  obtain ⟨Z, hZ_meas, hZ_edist, hZ_eq⟩ :=
    exists_modification_on_of_edist_modification_on hY_meas hY_edist
  refine ⟨Z, hZ_meas, hZ_eq, fun ω ↦ ?_, ?_⟩
  · specialize hY_holder ω
    obtain ⟨C, hC⟩ := hY_holder
    refine ⟨C, ?_⟩
    refine hC.congr_edist fun s t hs ht ↦ ?_
    rw [edist_congr_left (hZ_edist t ω), edist_congr_right (hZ_edist s ω)]
  · obtain ⟨A, hA_meas, hA_ae, hY_tendsto, hYU, hYUc⟩ := hY_limit
    refine ⟨A, hA_meas, hA_ae, hY_tendsto, fun t htU ω ↦ ?_, fun t htU ω ↦ ?_⟩
    · specialize hYU t htU ω
      refine le_antisymm ?_ zero_le
      refine (edist_triangle _ (Y t ω) _).trans ?_
      simpa [hZ_edist]
    · specialize hYUc t htU ω
      refine le_antisymm ?_ zero_le
      refine (edist_triangle _ (Y t ω) _).trans ?_
      simpa [hZ_edist]
lemma exists_modification_holder_aux (hT : HasBoundedCoveringNumber U c d)
    (hU : IsOpen U)
    (hX : IsAEKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t ∈ U, Y t =ᵐ[P] X t)∧
      ∀ ω, ∃ C : ℝ≥0, HolderOnWith C β (Y · ω) U := by
  obtain ⟨Y, hY_meas, hY_eq, hY_holder, _⟩ :=
    exists_modification_holder_aux' hT hU hX.IsKolmogorovProcess_mk hc hd_pos hdq_lt
      hβ_pos hβ_lt
  refine ⟨Y, hY_meas, fun t htU ↦ ?_, hY_holder⟩
  filter_upwards [hX.ae_eq_mk t, hY_eq t htU] with ω hω1 hω2 using hω2.trans hω1.symm
open TopologicalSpace in
lemma indistinguishable_of_edist_modification_on {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [PseudoEMetricSpace E] [TopologicalSpace T]
    [SeparableSpace T] {P : Measure Ω} {U : Set T} (hU : IsOpen U)
    {X Y : T → Ω → E}
    (hX : ∀ᵐ ω ∂P, ContinuousOn (X · ω) U) (hY : ∀ᵐ ω ∂P, ContinuousOn (Y · ω) U)
    (h : ∀ t ∈ U, ∀ᵐ ω ∂P, edist (X t ω) (Y t ω) = 0) :
    ∀ᵐ ω ∂P, ∀ t ∈ U, edist (X t ω) (Y t ω) = 0 := by
  let ⟨D, D_countable, D_dense⟩ := ‹SeparableSpace T›
  have DU_countable : (D ∩ U).Countable := D_countable.mono Set.inter_subset_left
  have eq (ht : ∀ t ∈ (D ∩ U), ∀ᵐ ω ∂P, edist (X t ω) (Y t ω) = 0) :
      ∀ᵐ ω ∂P, ∀ t ∈ (D ∩ U), edist (X t ω) (Y t ω) = 0 := (ae_ball_iff DU_countable).mpr ht
  filter_upwards [hX, hY, eq (fun t ht ↦ h t ht.2)] with ω hX hY h t htU
  suffices Set.EqOn (fun t ↦ edist (X t ω) (Y t ω)) 0 U from this htU
  refine Set.EqOn.of_subset_closure h ?_ (by fun_prop) Set.inter_subset_right ?_
  · intro s hsU
    exact (hX s hsU).edist (hY s hsU)
  exact subset_closure_dense_inter D_dense hU
open TopologicalSpace in
lemma indistinguishable_of_edist_modification {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [PseudoEMetricSpace E] [TopologicalSpace T]
    [SeparableSpace T] {P : Measure Ω}
    {X Y : T → Ω → E}
    (hX : ∀ᵐ ω ∂P, Continuous (X · ω)) (hY : ∀ᵐ ω ∂P, Continuous (Y · ω))
    (h : ∀ t, ∀ᵐ ω ∂P, edist (X t ω) (Y t ω) = 0) :
    ∀ᵐ ω ∂P, ∀ t, edist (X t ω) (Y t ω) = 0 := by
  suffices ∀ᵐ ω ∂P, ∀ t ∈ Set.univ, edist (X t ω) (Y t ω) = 0 by simpa using this
  exact indistinguishable_of_edist_modification_on isOpen_univ (by simpa) (by simpa) (by simpa)
end PseudoEMetricSpace

section EMetricSpace

variable [PseudoEMetricSpace T] [EMetricSpace E] [hE : Nonempty E]

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [SecondCountableTopology T]

variable [IsFiniteMeasure P]

end EMetricSpace

end ProbabilityTheory


