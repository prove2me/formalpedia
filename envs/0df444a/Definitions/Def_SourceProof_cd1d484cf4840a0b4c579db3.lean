-- Prove2me | Definitions.Def_SourceProof_cd1d484cf4840a0b4c579db3
-- name    : SourceProof_cd1d484cf4840a0b4c579db3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:51:47.131085+00:00
-- url     : https://prove2.me/theorems/131f90a4-e264-48b9-991c-ca5d28ebd9b6
-- title:
--   StochLean source theorem: StochLean.LocallyFinitePartition.quadraticVariationSum_restrict_eq_stop

import Definitions.Def_StochLean_Analysis_PathVariation_AdmissiblePartition_F005
import Definitions.Def_StochLean_Analysis_PathVariation_Stopping_F000
import Definitions.Def_SourceProof_51202d8bd6fc2fc133a2c10d
import Definitions.Def_SourceProof_564697e1323307dfe37a6d6d

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Exact transport between finite and infinite partition restrictions

Stopping an enclosing finite restriction repeats its terminal endpoint. Direct restriction
deduplicates that endpoint. Endpoint-set invariance proves exact equality of their sums.
-/

@[expose] public section

open Set
open scoped NNReal

namespace StochLean.LocallyFinitePartition

theorem _root_.Prove2MeSourceProof.h_cd1d484cf4840a0b4c579db3 (π : LocallyFinitePartition)
    {s T : ℝ≥0} (hs : s ≤ T) (f : ℝ≥0 → ℝ) :
    quadraticVariationSum (π.restrict s) f =
      quadraticVariationSum (π.restrict T) (fun t ↦ f (min t s)) :=
  _root_.Prove2MeSourceProof.h_51202d8bd6fc2fc133a2c10d ((_root_.Prove2MeSourceProof.h_564697e1323307dfe37a6d6d π) hs).symm f
end StochLean.LocallyFinitePartition


