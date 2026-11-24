-- Prove2me | Definitions.Def_SourceProof_06cc3ff1ef6885939f260693
-- name    : SourceProof_06cc3ff1ef6885939f260693
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:38.647353+00:00
-- url     : https://prove2.me/theorems/ac1ffc92-7a12-4efb-8ebc-e6f1bba0d84b
-- title:
--   StochLean source theorem: StochLean.TimePartition.pointNat_fin

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

theorem _root_.Prove2MeSourceProof.h_06cc3ff1ef6885939f260693 (π : TimePartition T) (i : Fin (π.size + 1)) :
    π.pointNat i = π.point i := by
  simp only [StochLean.TimePartition.pointNat, min_eq_left (Nat.le_of_lt_succ i.isLt)]
end StochLean.TimePartition


