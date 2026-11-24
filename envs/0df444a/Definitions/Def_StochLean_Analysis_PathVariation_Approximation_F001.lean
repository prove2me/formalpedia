-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F001
-- name    : StochLean_Analysis_PathVariation_Approximation_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:47.912497+00:00
-- url     : https://prove2.me/theorems/418e0df4-b3a8-4bb8-8481-11685b9c684b
-- title:
--   StochLean: Analysis.PathVariation.Approximation F001

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

/-- Indices at or above the requested time, truncated to the horizon. -/
noncomputable def upperIndices (π : TimePartition T) (t : ℝ≥0) :
    Finset (Fin (π.size + 1)) :=
  Finset.univ.filter fun i ↦ min t T ≤ π.point i
end StochLean.TimePartition


