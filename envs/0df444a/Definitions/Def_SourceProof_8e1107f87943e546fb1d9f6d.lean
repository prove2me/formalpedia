-- Prove2me | Definitions.Def_SourceProof_8e1107f87943e546fb1d9f6d
-- name    : SourceProof_8e1107f87943e546fb1d9f6d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:59:28.48409+00:00
-- url     : https://prove2.me/theorems/50aaaa0b-359b-49d9-8b41-0d32b479a889
-- title:
--   StochLean source theorem: StochLean.TimePartition.mesh_stop_le

import Definitions.Def_SourceProof_62c96c8989b32380830efb77
import Definitions.Def_SourceProof_a6e27fccb43f3d164b030720

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

theorem _root_.Prove2MeSourceProof.h_8e1107f87943e546fb1d9f6d (π : TimePartition T) (hs : s ≤ T) :
    (π.stop s hs).mesh ≤ π.mesh :=
  Finset.sup_le (fun i _ ↦ ((_root_.Prove2MeSourceProof.h_a6e27fccb43f3d164b030720 π) hs i).trans ((_root_.Prove2MeSourceProof.h_62c96c8989b32380830efb77 π) i))
end TimePartition

end StochLean


