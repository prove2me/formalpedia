-- Prove2me | Definitions.Def_SourceProof_b56782530437a70393044b28
-- name    : SourceProof_b56782530437a70393044b28
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:40.201431+00:00
-- url     : https://prove2.me/theorems/58d2007b-cefd-4b1d-93f0-420a87925095
-- title:
--   StochLean source theorem: MeasureTheory.IsStoppingTime.measurableSet_inter_lt_before

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Probability_Process_Stopping_BeforeSigmaOrder_F000
import Definitions.Def_SourceProof_dfa9835b65113f9bb1f932de

open private exists_rat_between_withTop from Definitions.Def_StochLean_Probability_Process_Stopping_BeforeSigmaOrder_F000
/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Strict comparison events in the pre-stopping sigma-field

Protter III.7 uses a countable union over deterministic times strictly between
the two stopping times. Infinite upper times are allowed. Terminal information
is also measurable before `T` after restriction to `{T = ∞}`.
-/

@[expose] public section

open Set
open scoped NNReal

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
variable {σ τ : Ω → WithTop ℝ≥0}


theorem _root_.Prove2MeSourceProof.h_b56782530437a70393044b28 (hσ : IsStoppingTime F σ)
    (hτ : IsStoppingTime F τ) {A : Set Ω} (hA : MeasurableSet[hσ.measurableSpace] A) :
    MeasurableSet[hτ.measurableSpaceBefore] (A ∩ {ω | σ ω < τ ω}) := by
  have he : A ∩ {ω | σ ω < τ ω} = ⋃ q : ℚ,
      (A ∩ {ω | σ ω ≤ (Real.toNNReal q : WithTop ℝ≥0)}) ∩
        {ω | (Real.toNNReal q : WithTop ℝ≥0) < τ ω} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hω, hlt⟩
      obtain ⟨q, hq, hq'⟩ := exists_rat_between_withTop hlt
      exact ⟨q, ⟨hω, hq.le⟩, hq'⟩
    · rintro ⟨q, ⟨hω, hq⟩, hq'⟩
      exact ⟨hω, hq.trans_lt hq'⟩
  rw [he]
  exact MeasurableSet.iUnion fun q ↦ (_root_.Prove2MeSourceProof.h_dfa9835b65113f9bb1f932de hτ) _ (hA.2 _)
end MeasureTheory.IsStoppingTime


