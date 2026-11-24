-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F000
-- name    : StochLean_Analysis_PathVariation_Approximation_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:16:06.755577+00:00
-- url     : https://prove2.me/theorems/676df77e-162a-43a8-8675-34fef9fe4b6d
-- title:
--   StochLean: Analysis.PathVariation.Approximation F000

import Definitions.Def_StochLean_Analysis_PathVariation_Oscillation_F000
import Mathlib.Data.Finset.Max

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

/-- Extend the finite endpoint list constantly after its last index. -/
def pointNat (π : TimePartition T) (n : ℕ) : ℝ≥0 :=
  π.point ⟨min n π.size, Nat.lt_succ_of_le (min_le_right _ _)⟩
end StochLean.TimePartition


