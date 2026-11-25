-- Prove2me | Definitions.Def_SourceProof_a62151d8cfcf3df9208265cb
-- name    : SourceProof_a62151d8cfcf3df9208265cb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:37:53.448132+00:00
-- url     : https://prove2.me/theorems/f8066dcf-ba2f-56bd-abe2-e0e4d6e17d44
-- title:
--   StochLean source theorem: StochLean.TimePartition.pointNat_mem

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

theorem _root_.Prove2MeSourceProof.h_a62151d8cfcf3df9208265cb (π : TimePartition T) (n : ℕ) : π.pointNat n ∈ Set.range π.point :=
  ⟨_, rfl⟩
end StochLean.TimePartition


