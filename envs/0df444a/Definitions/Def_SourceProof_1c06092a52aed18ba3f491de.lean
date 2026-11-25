-- Prove2me | Definitions.Def_SourceProof_1c06092a52aed18ba3f491de
-- name    : SourceProof_1c06092a52aed18ba3f491de
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:10:32.208537+00:00
-- url     : https://prove2.me/theorems/5ea5953d-3339-5923-b5ef-4795f38641b2
-- title:
--   StochLean source theorem: ProbabilityTheory.IsAnnouncingSequence.measurableSpaceBefore_eq_iSup

import Definitions.Def_StochLean_Probability_Process_Stopping_AnnouncingSigma_F000
import Definitions.Def_SourceProof_51740884f3e4929ebdd46661
import Definitions.Def_SourceProof_6a0407047627b0386a56ee04
import Definitions.Def_SourceProof_b1ffca32a537cf74dad808cc
import Definitions.Def_SourceProof_b56782530437a70393044b28
import Definitions.Def_SourceProof_dfa9835b65113f9bb1f932de

open private measurableSet_congr_of_complete from Definitions.Def_StochLean_Probability_Process_Stopping_AnnouncingSigma_F000
/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The sigma-field of an announcing sequence

Protter III.6 uses only initial completeness, not right continuity of the
filtration. Both inclusions handle the source almost-sure convergence using
that completeness. The zero-lifetime event is retained explicitly.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory.IsAnnouncingSequence

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
variable {P : Measure Ω} {τ : Ω → WithTop ℝ≥0} {σ : ℕ → Ω → WithTop ℝ≥0}


theorem _root_.Prove2MeSourceProof.h_1c06092a52aed18ba3f491de (h : IsAnnouncingSequence F P τ σ)
    (hτ : IsStoppingTime F τ) (hc : IsCompleteSubMeasurableSpace P (F 0)) :
    hτ.measurableSpaceBefore = ⨆ n, (h.isStoppingTime n).measurableSpace := by
  have hcB : MeasureTheory.IsCompleteSubMeasurableSpace P hτ.measurableSpaceBefore :=
    fun A hA ↦ (_root_.Prove2MeSourceProof.h_6a0407047627b0386a56ee04 hτ) A (hc A hA)
  have h0 : F 0 ≤ ⨆ n, (h.isStoppingTime n).measurableSpace :=
    ((h.isStoppingTime 0).le_measurableSpace_of_const_le fun _ ↦ bot_le).trans
      (le_iSup (fun n ↦ (h.isStoppingTime n).measurableSpace) 0)
  have hcS : MeasureTheory.IsCompleteSubMeasurableSpace P (⨆ n, (h.isStoppingTime n).measurableSpace) :=
    fun A hA ↦ h0 A (hc A hA)
  apply le_antisymm
  · refine sup_le h0 (MeasurableSpace.generateFrom_le ?_)
    rintro _ ⟨t, A, hA, rfl⟩
    have hm : MeasurableSet[⨆ n, (h.isStoppingTime n).measurableSpace]
        (⋃ n, A ∩ {ω | (t : WithTop ℝ≥0) < σ n ω}) :=
      MeasurableSet.iUnion fun n ↦ le_iSup (fun n ↦ (h.isStoppingTime n).measurableSpace) n _
        ((_root_.Prove2MeSourceProof.h_51740884f3e4929ebdd46661 (h.isStoppingTime n)) _
          ((_root_.Prove2MeSourceProof.h_dfa9835b65113f9bb1f932de (h.isStoppingTime n)) t hA))
    apply measurableSet_congr_of_complete hcS hm
    filter_upwards [h.tendsto] with ω hω
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨n, hAω, hn⟩
      exact ⟨hAω, hn.trans_le ((h.monotone ω).ge_of_tendsto hω n)⟩
    · rintro ⟨hAω, ht⟩
      obtain ⟨n, hn⟩ := (hω.eventually (Ioi_mem_nhds ht)).exists
      exact ⟨n, hAω, hn⟩
  · refine iSup_le fun n A hA ↦ ?_
    have hlt := (_root_.Prove2MeSourceProof.h_b56782530437a70393044b28 (h.isStoppingTime n)) hτ hA
    have hz := (_root_.Prove2MeSourceProof.h_6a0407047627b0386a56ee04 hτ) _ (hA.2 0)
    apply measurableSet_congr_of_complete hcB (hlt.union hz)
    filter_upwards [(_root_.Prove2MeSourceProof.h_b1ffca32a537cf74dad808cc h)] with ω hω
    simp only [mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · exact fun hω ↦ hω.elim And.left And.left
    · intro hAω
      by_cases ht : 0 < τ ω
      · exact Or.inl ⟨hAω, h.strict n ω ht⟩
      · have he : τ ω = 0 := le_antisymm (le_of_not_gt ht) bot_le
        exact Or.inr ⟨hAω, (hω he n).le⟩
end ProbabilityTheory.IsAnnouncingSequence


