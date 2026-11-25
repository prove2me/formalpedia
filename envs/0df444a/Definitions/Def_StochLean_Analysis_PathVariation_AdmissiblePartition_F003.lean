-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_AdmissiblePartition_F003
-- name    : StochLean_Analysis_PathVariation_AdmissiblePartition_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:32:15.065121+00:00
-- url     : https://prove2.me/theorems/6d24fc41-f363-47f4-a0ef-567f5e8c5be4
-- title:
--   StochLean: Analysis.PathVariation.AdmissiblePartition F003

import Definitions.Def_StochLean_Analysis_PathVariation_AdmissiblePartition_F000
import Definitions.Def_StochLean_Analysis_PathVariation_AdmissiblePartition_F002
import Definitions.Def_SourceProof_013e30f47ef96f3395ad5153
import Definitions.Def_SourceProof_2e7fbc33aef6a7e578f19ded
import Definitions.Def_SourceProof_e212482f297d62b0d773b5b6

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

noncomputable def restrict (P : LocallyFinitePartition) (T : ℝ≥0) : TimePartition T :=
  TimePartition.ofFinset (P.restrictFinset T) ((_root_.Prove2MeSourceProof.h_2e7fbc33aef6a7e578f19ded P) T)
    ((_root_.Prove2MeSourceProof.h_e212482f297d62b0d773b5b6 P) T) ((_root_.Prove2MeSourceProof.h_013e30f47ef96f3395ad5153 P) T)
end LocallyFinitePartition

end StochLean


