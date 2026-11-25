-- Prove2me | Definitions.Def_SourceProof_bd0fe3b017a364f85ef29095
-- name    : SourceProof_bd0fe3b017a364f85ef29095
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T08:00:49.351384+00:00
-- url     : https://prove2.me/theorems/c62f29cc-27a9-43d7-ae2e-c2bce19a2d44
-- title:
--   StochLean source theorem: StochLean.TimePartition.right_le_left_of_lt

import Definitions.Def_StochLean_Analysis_PathVariation_CompletedSums_F001

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# The last partial cell has uniformly vanishing error

All partitions have the same enclosing horizon. Stopping a deterministic path
at an earlier time gives its usual partial square/cross sum; the difference
from completed-cell sums is confined to at most one cell. Continuity and
vanishing mesh make this difference uniformly small over the entire horizon.
-/

@[expose] public section

open Filter Finset Set
open scoped NNReal ENNReal Topology

namespace StochLean

variable {T : ℝ≥0}

namespace TimePartition
theorem _root_.Prove2MeSourceProof.h_bd0fe3b017a364f85ef29095 (π : TimePartition T) {i j : Fin π.size}
    (hij : i < j) : π.right i ≤ π.left j :=
  π.monotone_point (show i.succ ≤ j.castSucc from hij)
end TimePartition

end StochLean


