-- Prove2me | Definitions.Def_SourceProof_412fe430ffd916cdb8b0076b
-- name    : SourceProof_412fe430ffd916cdb8b0076b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:15:31.276477+00:00
-- url     : https://prove2.me/theorems/ef241e46-f73e-4634-b09b-2f24eb95529f
-- title:
--   StochLean source theorem: StochLean.LocallyFinitePartition.mem_restrictFinset

import Definitions.Def_StochLean_Analysis_PathVariation_AdmissiblePartition_F002

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

theorem _root_.Prove2MeSourceProof.h_412fe430ffd916cdb8b0076b (P : LocallyFinitePartition) (T t : ℝ≥0) :
    t ∈ P.restrictFinset T ↔ t = T ∨ t ∈ P.points ∧ t ≤ T := by
  simp [StochLean.LocallyFinitePartition.restrictFinset]
end LocallyFinitePartition

end StochLean


