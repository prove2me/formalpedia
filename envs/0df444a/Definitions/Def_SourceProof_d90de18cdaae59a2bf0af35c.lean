-- Prove2me | Definitions.Def_SourceProof_d90de18cdaae59a2bf0af35c
-- name    : SourceProof_d90de18cdaae59a2bf0af35c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:37.20747+00:00
-- url     : https://prove2.me/theorems/e9ee674c-5bf2-4c1a-9d41-93b545581cb0
-- title:
--   StochLean source theorem: StochLean.TimePartition.ceilingIndex_le

import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F002

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

theorem _root_.Prove2MeSourceProof.h_d90de18cdaae59a2bf0af35c (π : TimePartition T) {t : ℝ≥0} {i : Fin (π.size + 1)}
    (hi : min t T ≤ π.point i) : π.ceilingIndex t ≤ i := by
  classical
  unfold StochLean.TimePartition.ceilingIndex
  apply Finset.min'_le
  simp only [StochLean.TimePartition.upperIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hi
end StochLean.TimePartition


