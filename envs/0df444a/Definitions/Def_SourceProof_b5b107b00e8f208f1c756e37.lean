-- Prove2me | Definitions.Def_SourceProof_b5b107b00e8f208f1c756e37
-- name    : SourceProof_b5b107b00e8f208f1c756e37
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T08:00:28.210439+00:00
-- url     : https://prove2.me/theorems/4f5472f2-0a95-42ef-bc10-3d4d67731234
-- title:
--   StochLean source theorem: StochLean.TimePartition.ceilingIndex_mono

import Definitions.Def_SourceProof_41c8e0f72444e5cb2bd104fc
import Definitions.Def_SourceProof_d90de18cdaae59a2bf0af35c

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

theorem _root_.Prove2MeSourceProof.h_b5b107b00e8f208f1c756e37 (π : TimePartition T) : Monotone π.ceilingIndex := by
  intro s t hst
  exact (_root_.Prove2MeSourceProof.h_d90de18cdaae59a2bf0af35c π) ((min_le_min_right T hst).trans ((_root_.Prove2MeSourceProof.h_41c8e0f72444e5cb2bd104fc π) t))
end StochLean.TimePartition


