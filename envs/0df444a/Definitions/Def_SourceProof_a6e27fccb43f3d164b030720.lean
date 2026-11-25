-- Prove2me | Definitions.Def_SourceProof_a6e27fccb43f3d164b030720
-- name    : SourceProof_a6e27fccb43f3d164b030720
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:46:12.633581+00:00
-- url     : https://prove2.me/theorems/b6721c0a-2e30-4524-ba22-f2147766941c
-- title:
--   StochLean source theorem: StochLean.TimePartition.gap_stop_le

import Definitions.Def_StochLean_Analysis_PathVariation_Stopping_F000
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Deterministic stopping of finite partitions

Clipping every endpoint retains repeated endpoints. This avoids arbitrary deduplication in
the pathwise stopping identity and preserves refinement and the vanishing-mesh condition.
-/

@[expose] public section

open Filter Set Finset
open scoped NNReal Topology

namespace StochLean

namespace TimePartition

variable {T s : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_a6e27fccb43f3d164b030720 (π : TimePartition T) (hs : s ≤ T) (i : Fin π.size) :
    (π.stop s hs).gap i ≤ π.gap i := by
  change min (π.right i) s - min (π.left i) s ≤ π.right i - π.left i
  by_cases hl : π.left i ≤ s
  · rw [min_eq_left hl]
    exact tsub_le_tsub_right (min_le_left _ _) _
  · have hr : s ≤ π.right i := (le_of_not_ge hl).trans ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 π) i)
    rw [min_eq_right hr, min_eq_right (le_of_not_ge hl), tsub_self]
    exact bot_le
end TimePartition

end StochLean


