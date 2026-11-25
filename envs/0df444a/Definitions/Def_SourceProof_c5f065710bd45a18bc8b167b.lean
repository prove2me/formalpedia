-- Prove2me | Definitions.Def_SourceProof_c5f065710bd45a18bc8b167b
-- name    : SourceProof_c5f065710bd45a18bc8b167b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:24.31757+00:00
-- url     : https://prove2.me/theorems/8a7cb8d6-f359-5f47-88d4-b10fe8424532
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPredictableStoppingTime.measurableSet_eq_before

import Definitions.Def_StochLean_Probability_Process_Stopping_Announcing_F000
import Definitions.Def_SourceProof_7afbc88789b9bcaafb30a87c
import Definitions.Def_SourceProof_dee3670cfc13659d234d1315

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

theorem _root_.Prove2MeSourceProof.h_c5f065710bd45a18bc8b167b
    (hσ : IsPredictableStoppingTime F σ P) (hτ : IsStoppingTime F τ)
    (hc0 : IsCompleteSubMeasurableSpace P (F 0)) :
    MeasurableSet[hτ.measurableSpaceBefore] {ω | σ ω = τ ω} := by
  have he : {ω | σ ω = τ ω} = {ω | σ ω ≤ τ ω} \ {ω | σ ω < τ ω} := by
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    exact ⟨fun h ↦ ⟨h.le, not_lt_of_ge h.ge⟩,
      fun h ↦ le_antisymm h.1 (le_of_not_gt h.2)⟩
  rw [he]
  exact ((_root_.Prove2MeSourceProof.h_dee3670cfc13659d234d1315 hσ) hτ hc0).diff ((_root_.Prove2MeSourceProof.h_7afbc88789b9bcaafb30a87c hσ.1) hτ)
end IsPredictableStoppingTime

end ProbabilityTheory


