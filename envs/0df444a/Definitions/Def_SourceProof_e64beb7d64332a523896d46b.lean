-- Prove2me | Definitions.Def_SourceProof_e64beb7d64332a523896d46b
-- name    : SourceProof_e64beb7d64332a523896d46b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:44:03.893823+00:00
-- url     : https://prove2.me/theorems/a45ada2a-62f4-586a-aff6-1059b7ea3bb0
-- title:
--   StochLean source theorem: StochLean.TimePartition.ceilingPoint_mono

import Definitions.Def_SourceProof_b5b107b00e8f208f1c756e37

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

theorem _root_.Prove2MeSourceProof.h_e64beb7d64332a523896d46b (π : TimePartition T) : Monotone π.ceilingPoint :=
  π.monotone_point.comp (_root_.Prove2MeSourceProof.h_b5b107b00e8f208f1c756e37 π)
end StochLean.TimePartition


