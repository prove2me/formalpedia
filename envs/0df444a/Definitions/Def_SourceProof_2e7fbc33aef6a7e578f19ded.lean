-- Prove2me | Definitions.Def_SourceProof_2e7fbc33aef6a7e578f19ded
-- name    : SourceProof_2e7fbc33aef6a7e578f19ded
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:25:50.026295+00:00
-- url     : https://prove2.me/theorems/faffaba4-fc10-49d2-be73-cbd9c6f2b19f
-- title:
--   StochLean source theorem: StochLean.LocallyFinitePartition.zero_mem_restrictFinset

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

theorem _root_.Prove2MeSourceProof.h_2e7fbc33aef6a7e578f19ded (P : LocallyFinitePartition) (T : ℝ≥0) :
    0 ∈ P.restrictFinset T :=
  ((_root_.Prove2MeSourceProof.h_412fe430ffd916cdb8b0076b P) T 0).mpr (Or.inr ⟨P.zero_mem, bot_le⟩)
end LocallyFinitePartition

end StochLean


