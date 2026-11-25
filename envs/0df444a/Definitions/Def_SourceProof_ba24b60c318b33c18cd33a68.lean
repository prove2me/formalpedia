-- Prove2me | Definitions.Def_SourceProof_ba24b60c318b33c18cd33a68
-- name    : SourceProof_ba24b60c318b33c18cd33a68
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T08:00:37.734814+00:00
-- url     : https://prove2.me/theorems/1d173330-e624-4254-8128-3fbbcc89a5ba
-- title:
--   StochLean source theorem: StochLean.quadraticVariationSum_stop

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

end TimePartition

theorem _root_.Prove2MeSourceProof.h_ba24b60c318b33c18cd33a68 {T s : ℝ≥0} (π : TimePartition T) (hs : s ≤ T)
    (f : ℝ≥0 → ℝ) :
    quadraticVariationSum (π.stop s hs) f =
      quadraticVariationSum π (fun t ↦ f (min t s)) := rfl
end StochLean


