-- Prove2me | Definitions.Def_SourceProof_40c22f8cb9dd1f12ac3b079a
-- name    : SourceProof_40c22f8cb9dd1f12ac3b079a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:35:22.483042+00:00
-- url     : https://prove2.me/theorems/c566522a-d7e4-51b6-a3a2-b9b699670cbd
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.measurable_strictLeftGrid_sample

import Definitions.Def_StochLean_Probability_Process_Measurability_PredictableGrid_F000
import Definitions.Def_SourceProof_404ac7688bf4951a8244ece2
import Definitions.Def_SourceProof_450d12110808f2b6e6c7e25f
import Definitions.Def_SourceProof_7a587c2d7b097459d1fe61a8

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Strict-past deterministic grids for predictable processes

At a positive grid endpoint the preceding cell is used, as required for predictable
`(s,t]` rectangles. At zero the original initial value is retained.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_40c22f8cb9dd1f12ac3b079a (ha : Adapted F X)
    {δ : ℝ≥0} (hδ : 0 < δ) :
    Measurable[F.predictable] (fun z : ℝ≥0 × Ω ↦ X (strictLeftGrid δ z.1) z.2) := by
  intro s hs
  have heq : (fun z : ℝ≥0 × Ω ↦ X (ProbabilityTheory.strictLeftGrid δ z.1) z.2) ⁻¹' s =
      ({0} ×ˢ ((X 0) ⁻¹' s)) ∪
        ⋃ k : ℕ, Ioc (δ * k) (δ * (k + 1)) ×ˢ ((X (δ * k)) ⁻¹' s) := by
    ext ⟨t, ω⟩
    constructor
    · intro h
      by_cases ht : t = 0
      · left
        simpa only [ht, mem_prod, mem_singleton_iff, _root_.Prove2MeSourceProof.h_404ac7688bf4951a8244ece2, mem_preimage,
          true_and] using h
      · right
        let k := Nat.ceil (t / δ) - 1
        apply mem_iUnion.mpr ⟨k, ?_⟩
        have hcell := _root_.Prove2MeSourceProof.h_7a587c2d7b097459d1fe61a8 hδ (pos_iff_ne_zero.mpr ht)
        refine ⟨?_, h⟩
        simpa only [ProbabilityTheory.strictLeftGrid, k, mul_add, mul_one] using hcell
    · rintro (h | h)
      · rcases h with ⟨ht, hω⟩
        have ht' : t = 0 := ht
        change X (ProbabilityTheory.strictLeftGrid δ t) ω ∈ s
        simpa only [ht', _root_.Prove2MeSourceProof.h_404ac7688bf4951a8244ece2, mem_preimage] using hω
      · obtain ⟨k, hk, hω⟩ := mem_iUnion.mp h
        change X (ProbabilityTheory.strictLeftGrid δ t) ω ∈ s
        simpa only [_root_.Prove2MeSourceProof.h_450d12110808f2b6e6c7e25f hδ k hk, mem_preimage] using hω
  rw [heq]
  exact (measurableSet_predictable_singleton_bot_prod (ha 0 hs)).union
    (MeasurableSet.iUnion (fun k ↦ measurableSet_predictable_Ioc_prod _ _ (ha _ hs)))
end Adapted

end MeasureTheory


