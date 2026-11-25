-- Prove2me | Definitions.Def_SourceProof_e3ad00054b225b26545121b0
-- name    : SourceProof_e3ad00054b225b26545121b0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:28.175802+00:00
-- url     : https://prove2.me/theorems/41eeac83-0d13-5979-bf9b-65bab86cf80d
-- title:
--   StochLean source theorem: StochLean.TimePartition.image_pointNat_Iic

import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F000
import Definitions.Def_SourceProof_06cc3ff1ef6885939f260693
import Definitions.Def_SourceProof_a62151d8cfcf3df9208265cb

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

theorem _root_.Prove2MeSourceProof.h_e3ad00054b225b26545121b0 (π : TimePartition T) :
    π.pointNat '' Iic π.size = Set.range π.point := by
  ext t
  constructor
  · rintro ⟨n, _, rfl⟩
    exact (_root_.Prove2MeSourceProof.h_a62151d8cfcf3df9208265cb π) n
  · rintro ⟨i, rfl⟩
    exact ⟨i, Nat.le_of_lt_succ i.isLt, (_root_.Prove2MeSourceProof.h_06cc3ff1ef6885939f260693 π) i⟩
end StochLean.TimePartition


