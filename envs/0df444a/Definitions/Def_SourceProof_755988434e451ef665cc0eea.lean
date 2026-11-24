-- Prove2me | Definitions.Def_SourceProof_755988434e451ef665cc0eea
-- name    : SourceProof_755988434e451ef665cc0eea
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:13.994256+00:00
-- url     : https://prove2.me/theorems/0b91b12e-24fb-4cd6-9e6f-56bf7e593980
-- title:
--   StochLean source theorem: StochLean.TimePartition.pointNat_mono

import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F000

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

theorem _root_.Prove2MeSourceProof.h_755988434e451ef665cc0eea (π : TimePartition T) : Monotone π.pointNat := by
  intro n m hnm
  apply π.monotone_point
  exact min_le_min_right _ hnm
end StochLean.TimePartition


