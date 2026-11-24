-- Prove2me | Definitions.Def_SourceProof_2da1122e2444d9d7e9c19b99
-- name    : SourceProof_2da1122e2444d9d7e9c19b99
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:20:57.351289+00:00
-- url     : https://prove2.me/theorems/8b03905f-58c7-4031-9e7d-ffb350e46ff7
-- title:
--   StochLean source theorem: StochLean.TimePartition.ceilingPoint_tendsto

import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F002
import Definitions.Def_SourceProof_31206da94e8ad4f6bba4c1fa

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Endpoint approximations for finite partitions

The right endpoint projection is monotone, remains in the original endpoint
set, and is at distance at most the mesh on the compact horizon. This is a
deterministic approximation: no extra grid is inserted.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_2da1122e2444d9d7e9c19b99 {π : ℕ → TimePartition T}
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) {t : ℝ≥0} (ht : t ≤ T) :
    Tendsto (fun n ↦ (π n).ceilingPoint t) atTop (𝓝 t) := by
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ (_root_.Prove2MeSourceProof.h_31206da94e8ad4f6bba4c1fa (π n)) ht) hmesh
end StochLean.TimePartition


