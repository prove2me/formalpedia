-- Prove2me | Definitions.Def_SourceProof_73fd652f96ace405ff62d22b
-- name    : SourceProof_73fd652f96ace405ff62d22b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:30:51.509978+00:00
-- url     : https://prove2.me/theorems/7695cfe8-bf36-44a5-b862-0a838326e5f6
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCagladPath.exists_norm_bound_on_compact

import Definitions.Def_SourceProof_8d69b22c19a0d6fad9033e2a

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Local and compact bounds for caglad paths

Left continuity and finite right limits jointly give an ordinary neighborhood
bound, including at time zero. A compact subcover gives the finite-horizon bound.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] {x : ℝ≥0 → E}

namespace IsCagladPath
theorem _root_.Prove2MeSourceProof.h_73fd652f96ace405ff62d22b (hx : IsCagladPath x)
    {K : Set ℝ≥0} (hK : IsCompact K) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ K, ‖x t‖ ≤ C := by
  classical
  choose C hCpos hC using (_root_.Prove2MeSourceProof.h_8d69b22c19a0d6fad9033e2a hx)
  obtain ⟨s, _, hs⟩ := hK.elim_nhds_subcover (fun t ↦ {u | ‖x u‖ ≤ C t}) (fun t _ ↦ hC t)
  refine ⟨∑ t ∈ s, C t, Finset.sum_nonneg (fun t _ ↦ hCpos t), ?_⟩
  intro t ht
  obtain ⟨u, hu, hut⟩ := mem_iUnion₂.mp (hs ht)
  exact hut.trans (Finset.single_le_sum (fun v _ ↦ hCpos v) hu)
end IsCagladPath

end ProbabilityTheory


