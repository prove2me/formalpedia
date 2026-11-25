-- Prove2me | Definitions.Def_SourceProof_b5697f710fe6829a60e25fdb
-- name    : SourceProof_b5697f710fe6829a60e25fdb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:13:59.530824+00:00
-- url     : https://prove2.me/theorems/367d1fe6-67ce-5eef-b56d-ff9f7e3a31db
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.exists_norm_bound_on_compact

import Definitions.Def_SourceProof_dcdb768b8cb5c9b21a01f5b9

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Local and compact bounds for cadlag paths

The lower endpoint is treated by right continuity alone. At positive times,
the actual finite left limit and right continuity give a neighborhood bound.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] {x : ℝ≥0 → E}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_b5697f710fe6829a60e25fdb (hx : IsCadlagPath x)
    {K : Set ℝ≥0} (hK : IsCompact K) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ K, ‖x t‖ ≤ C := by
  classical
  choose C hCpos hC using (_root_.Prove2MeSourceProof.h_dcdb768b8cb5c9b21a01f5b9 hx)
  obtain ⟨s, _, hs⟩ := hK.elim_nhds_subcover (fun t ↦ {u | ‖x u‖ ≤ C t}) (fun t _ ↦ hC t)
  refine ⟨∑ t ∈ s, C t, Finset.sum_nonneg (fun t _ ↦ hCpos t), ?_⟩
  intro t ht
  obtain ⟨u, hu, hut⟩ := mem_iUnion₂.mp (hs ht)
  exact hut.trans (Finset.single_le_sum (fun v _ ↦ hCpos v) hu)
end IsCadlagPath

end ProbabilityTheory


