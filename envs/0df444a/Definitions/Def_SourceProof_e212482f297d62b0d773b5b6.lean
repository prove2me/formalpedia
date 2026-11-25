-- Prove2me | Definitions.Def_SourceProof_e212482f297d62b0d773b5b6
-- name    : SourceProof_e212482f297d62b0d773b5b6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:25:43.165502+00:00
-- url     : https://prove2.me/theorems/3fae54fa-c751-5592-bd78-aa6d33a916e8
-- title:
--   StochLean source theorem: StochLean.LocallyFinitePartition.horizon_mem_restrictFinset

import Definitions.Def_StochLean_Analysis_PathVariation_AdmissiblePartition_F002
import Definitions.Def_SourceProof_412fe430ffd916cdb8b0076b

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Locally finite deterministic partitions and finite-horizon restriction

An infinite partition is stored as its set of endpoints. Restriction to `[0,T]`
keeps every original endpoint in that interval and adds only `T`. Its sorted
enumeration belongs to the same finite `TimePartition` owner used by random
partitions. Admissibility uses the maximum adjacent gap, not the insufficient
nearest-neighbor mesh printed in Klenke 21.56; see the source-correction ledger.
-/

@[expose] public section

open Filter Set Finset
open scoped NNReal ENNReal Topology

namespace StochLean

namespace TimePartition

end TimePartition

namespace LocallyFinitePartition

theorem _root_.Prove2MeSourceProof.h_e212482f297d62b0d773b5b6 (P : LocallyFinitePartition) (T : ℝ≥0) :
    T ∈ P.restrictFinset T := ((_root_.Prove2MeSourceProof.h_412fe430ffd916cdb8b0076b P) T T).mpr (Or.inl rfl)
end LocallyFinitePartition

end StochLean


