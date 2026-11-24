-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_Stopping_F000
-- name    : StochLean_Analysis_PathVariation_Stopping_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:25:36.340241+00:00
-- url     : https://prove2.me/theorems/281fefc1-7e40-47b1-bb89-be794f48af97
-- title:
--   StochLean: Analysis.PathVariation.Stopping F000

import Definitions.Def_StochLean_Analysis_PathVariation_TotalVariation_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Deterministic stopping of finite partitions

Clipping every endpoint retains repeated endpoints. This avoids arbitrary deduplication in
the pathwise stopping identity and preserves refinement and the vanishing-mesh condition.
-/

@[expose] public section

open Filter Set Finset
open scoped NNReal Topology

namespace StochLean

namespace TimePartition

variable {T s : ℝ≥0}

/-- Stop a partition at an earlier horizon, keeping its original number of cells. -/
def stop (π : TimePartition T) (s : ℝ≥0) (hs : s ≤ T) : TimePartition s where
  size := π.size
  point i := min (π.point i) s
  monotone_point := fun _ _ hij ↦ min_le_min_right s (π.monotone_point hij)
  first_eq_zero := by simp [π.first_eq_zero]
  last_eq_horizon := by simp [π.last_eq_horizon, min_eq_right hs]
end TimePartition

end StochLean


