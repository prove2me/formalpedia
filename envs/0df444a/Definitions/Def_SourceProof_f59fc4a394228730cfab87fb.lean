-- Prove2me | Definitions.Def_SourceProof_f59fc4a394228730cfab87fb
-- name    : SourceProof_f59fc4a394228730cfab87fb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:39.941184+00:00
-- url     : https://prove2.me/theorems/645abf2d-3aec-4b40-a2f9-ef667b0e7647
-- title:
--   StochLean source theorem: StochLean.TimePartition.ceilingPoint_mem

import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F002

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

theorem _root_.Prove2MeSourceProof.h_f59fc4a394228730cfab87fb (π : TimePartition T) (t : ℝ≥0) :
    π.ceilingPoint t ∈ Set.range π.point := ⟨_, rfl⟩
end StochLean.TimePartition


