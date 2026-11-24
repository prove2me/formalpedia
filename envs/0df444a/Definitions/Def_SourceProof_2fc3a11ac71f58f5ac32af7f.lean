-- Prove2me | Definitions.Def_SourceProof_2fc3a11ac71f58f5ac32af7f
-- name    : SourceProof_2fc3a11ac71f58f5ac32af7f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:00.059837+00:00
-- url     : https://prove2.me/theorems/5ab17238-7c42-4903-a5d8-c7c65cd09abc
-- title:
--   StochLean source theorem: StochLean.TimePartition.upperIndices_nonempty

import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F001

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

theorem _root_.Prove2MeSourceProof.h_2fc3a11ac71f58f5ac32af7f (π : TimePartition T) (t : ℝ≥0) :
    (upperIndices π t).Nonempty := by
  classical
  exact ⟨Fin.last π.size, by simp [StochLean.TimePartition.upperIndices, π.last_eq_horizon]⟩
end StochLean.TimePartition


