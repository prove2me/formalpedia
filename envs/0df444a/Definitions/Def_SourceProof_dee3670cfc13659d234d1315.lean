-- Prove2me | Definitions.Def_SourceProof_dee3670cfc13659d234d1315
-- name    : SourceProof_dee3670cfc13659d234d1315
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:36:33.2951+00:00
-- url     : https://prove2.me/theorems/a92e1fc2-1192-4f91-830b-6a25453ca75f
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPredictableStoppingTime.measurableSet_le_before

import Definitions.Def_SourceProof_46e00cd1de49de31920230f6
import Definitions.Def_SourceProof_6a0407047627b0386a56ee04
import Definitions.Def_SourceProof_7afbc88789b9bcaafb30a87c
import Definitions.Def_SourceProof_963ead9a91977c0b480ddda0
import Definitions.Def_SourceProof_b631e7db21b69a2eea178eb7
import Definitions.Def_SourceProof_d6d3239f29afcc05f08f5261

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Comparison with a predictable time before a stopping time

If sigma is predictable and tau is a stopping time, then sigma <= tau is
measurable strictly before tau, provided the initial sigma-field contains
all ambient null sets. A capped announcing sequence gives the comparison
on the positive-tau event. The zero event is handled with initial information,
and completeness turns the almost-sure announcing equivalence into exact
measurability of the original comparison event.

Neither right continuity of the filtration, finiteness of the measure, nor
predictability of the second time is needed. Equality at infinity is allowed
in the equality theorem; the finite-equality theorem removes it explicitly.
These events can later support predictable restrictions and graph deduplication.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {σ τ : Ω → WithTop ℝ≥0}

namespace IsPredictableStoppingTime

theorem _root_.Prove2MeSourceProof.h_dee3670cfc13659d234d1315
    (hσ : IsPredictableStoppingTime F σ P) (hτ : IsStoppingTime F τ)
    (hc0 : IsCompleteSubMeasurableSpace P (F 0)) :
    MeasurableSet[hτ.measurableSpaceBefore] {ω | σ ω ≤ τ ω} := by
  classical
  obtain ⟨η, hη, hηle⟩ := (_root_.Prove2MeSourceProof.h_b631e7db21b69a2eea178eb7 hσ)
  have hσ0 : MeasurableSet[F 0] {ω | σ ω = 0} := by
    have he : {ω | σ ω = 0} = {ω | σ ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      exact ⟨fun h ↦ h.le, fun h ↦ le_antisymm h bot_le⟩
    rw [he]
    exact hσ.1 0
  have hτ0 : MeasurableSet[hτ.measurableSpaceBefore] {ω | τ ω = 0} :=
    (_root_.Prove2MeSourceProof.h_d6d3239f29afcc05f08f5261 hτ) (measurableSet_singleton 0)
  let E : Set Ω := ({ω | τ ω = 0} ∩ {ω | σ ω = 0}) ∪
    ({ω | 0 < τ ω} ∩ ⋂ n : ℕ, {ω | η n ω < τ ω})
  have hE : MeasurableSet[hτ.measurableSpaceBefore] E :=
    (hτ0.inter ((_root_.Prove2MeSourceProof.h_6a0407047627b0386a56ee04 hτ) _ hσ0)).union
      (((_root_.Prove2MeSourceProof.h_963ead9a91977c0b480ddda0 hτ) 0).inter
        (MeasurableSet.iInter fun n ↦ (_root_.Prove2MeSourceProof.h_7afbc88789b9bcaafb30a87c (hη.isStoppingTime n)) hτ))
  have he : ∀ᵐ ω ∂P, ω ∈ E ↔ σ ω ≤ τ ω := by
    filter_upwards [hη.tendsto] with ω hω
    simp only [E, mem_union, mem_inter_iff, mem_ofPred_eq, mem_iInter]
    constructor
    · rintro (⟨hτw, hσw⟩ | ⟨_, hlt⟩)
      · rw [hτw, hσw]
      · exact le_of_tendsto hω (Eventually.of_forall fun n ↦ (hlt n).le)
    · intro hστ
      by_cases hτpos : 0 < τ ω
      · refine Or.inr ⟨hτpos, fun n ↦ ?_⟩
        by_cases hσpos : 0 < σ ω
        · exact (hη.strict n ω hσpos).trans_le hστ
        · have hσw : σ ω = 0 := le_antisymm (le_of_not_gt hσpos) bot_le
          exact (hηle n ω).trans_lt (hσw.le.trans_lt hτpos)
      · have hτw : τ ω = 0 := le_antisymm (le_of_not_gt hτpos) bot_le
        exact Or.inl ⟨hτw, le_antisymm (hστ.trans hτw.le) bot_le⟩
  have hcB : MeasureTheory.IsCompleteSubMeasurableSpace P hτ.measurableSpaceBefore :=
    fun S hS ↦ (_root_.Prove2MeSourceProof.h_6a0407047627b0386a56ee04 hτ) S (hc0 S hS)
  have hχ : E.indicator (fun _ : Ω ↦ (1 : ℝ)) =ᵐ[P]
      {ω | σ ω ≤ τ ω}.indicator (fun _ : Ω ↦ (1 : ℝ)) := by
    filter_upwards [he] with ω hω
    simp only [indicator_apply, mem_ofPred_eq, hω]
  have hm := (_root_.Prove2MeSourceProof.h_46e00cd1de49de31920230f6 hcB) (measurable_const.indicator hE) hχ
  convert hm (measurableSet_singleton (1 : ℝ)) using 1
  ext ω
  simp [Set.indicator]
end IsPredictableStoppingTime

end ProbabilityTheory


