-- Prove2me | Definitions.Def_SourceProof_54f7c3a65933c3f46d82cbdc
-- name    : SourceProof_54f7c3a65933c3f46d82cbdc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:25.310641+00:00
-- url     : https://prove2.me/theorems/8776f407-adc8-45a4-a005-5d20bd375a2a
-- title:
--   StochLean source theorem: StochLean.TimePartition.ceilingPoint_le_horizon

import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F002
import Definitions.Def_SourceProof_2ba9ae385eb9bd368051c43f

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

theorem _root_.Prove2MeSourceProof.h_54f7c3a65933c3f46d82cbdc (π : TimePartition T) (t : ℝ≥0) :
    π.ceilingPoint t ≤ T := (_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f π) _
end StochLean.TimePartition


