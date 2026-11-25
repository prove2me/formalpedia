-- Prove2me | Definitions.Def_SourceProof_22d80a2190f136747d0e9643
-- name    : SourceProof_22d80a2190f136747d0e9643
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:36:19.334801+00:00
-- url     : https://prove2.me/theorems/c96bed4a-b06f-59b3-84d3-b4ba187829da
-- title:
--   StochLean source theorem: StochLean.LocallyFinitePartition.mem_range_restrict

import Definitions.Def_StochLean_Analysis_PathVariation_AdmissiblePartition_F003
import Definitions.Def_SourceProof_364291d12fb632d24ad6bc1d
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


theorem _root_.Prove2MeSourceProof.h_22d80a2190f136747d0e9643 (P : LocallyFinitePartition) (T t : ℝ≥0) :
    t ∈ Set.range (P.restrict T).point ↔ t = T ∨ t ∈ P.points ∧ t ≤ T := by
  rw [StochLean.LocallyFinitePartition.restrict, _root_.Prove2MeSourceProof.h_364291d12fb632d24ad6bc1d]
  exact (_root_.Prove2MeSourceProof.h_412fe430ffd916cdb8b0076b P) T t
end LocallyFinitePartition

end StochLean


