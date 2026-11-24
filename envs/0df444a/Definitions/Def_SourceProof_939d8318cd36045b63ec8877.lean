-- Prove2me | Definitions.Def_SourceProof_939d8318cd36045b63ec8877
-- name    : SourceProof_939d8318cd36045b63ec8877
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:44:45.225705+00:00
-- url     : https://prove2.me/theorems/73803b5f-d7cb-4def-b9db-f8f012c341d7
-- title:
--   StochLean source theorem: StochLean.TimePartition.Refines.stop

import Definitions.Def_StochLean_Analysis_PathVariation_Stopping_F000

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

namespace Refines
theorem _root_.Prove2MeSourceProof.h_939d8318cd36045b63ec8877 {π ρ : TimePartition T} (h : π.Refines ρ) (hs : s ≤ T) :
    (π.stop s hs).Refines (ρ.stop s hs) := by
  rintro t ⟨i, rfl⟩
  obtain ⟨j, hj⟩ := h ⟨i, rfl⟩
  exact ⟨j, congrArg (min · s) hj⟩
end Refines

end TimePartition

end StochLean


