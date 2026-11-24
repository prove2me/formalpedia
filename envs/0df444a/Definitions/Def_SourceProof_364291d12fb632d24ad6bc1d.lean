-- Prove2me | Definitions.Def_SourceProof_364291d12fb632d24ad6bc1d
-- name    : SourceProof_364291d12fb632d24ad6bc1d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:27.375921+00:00
-- url     : https://prove2.me/theorems/b0b84583-2b7b-481a-b6ae-9dd82962abfe
-- title:
--   StochLean source theorem: StochLean.TimePartition.ofFinset_range

import Definitions.Def_StochLean_Analysis_PathVariation_AdmissiblePartition_F000

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

theorem _root_.Prove2MeSourceProof.h_364291d12fb632d24ad6bc1d {T : ℝ≥0} (s : Finset ℝ≥0)
    (h0 : 0 ∈ s) (hT : T ∈ s) (hb : ∀ x ∈ s, x ≤ T) :
    Set.range (ofFinset s h0 hT hb).point = (s : Set ℝ≥0) :=
  s.range_orderEmbOfFin _
end TimePartition

namespace LocallyFinitePartition

end LocallyFinitePartition

end StochLean


