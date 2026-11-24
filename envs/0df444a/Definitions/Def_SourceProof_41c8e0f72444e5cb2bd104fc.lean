-- Prove2me | Definitions.Def_SourceProof_41c8e0f72444e5cb2bd104fc
-- name    : SourceProof_41c8e0f72444e5cb2bd104fc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:26.886804+00:00
-- url     : https://prove2.me/theorems/543b51bc-4297-4242-a0f9-3e6e67549779
-- title:
--   StochLean source theorem: StochLean.TimePartition.min_le_ceilingPoint

import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F002
import Definitions.Def_SourceProof_2fc3a11ac71f58f5ac32af7f

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

theorem _root_.Prove2MeSourceProof.h_41c8e0f72444e5cb2bd104fc (π : TimePartition T) (t : ℝ≥0) :
    min t T ≤ π.ceilingPoint t := by
  have h := Finset.min'_mem (StochLean.TimePartition.upperIndices π t) (_root_.Prove2MeSourceProof.h_2fc3a11ac71f58f5ac32af7f π t)
  simpa only [StochLean.TimePartition.upperIndices, Finset.mem_filter, Finset.mem_univ, true_and,
    StochLean.TimePartition.ceilingPoint, ceilingIndex] using h
end StochLean.TimePartition


