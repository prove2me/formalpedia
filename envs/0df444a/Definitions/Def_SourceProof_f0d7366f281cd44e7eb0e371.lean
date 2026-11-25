-- Prove2me | Definitions.Def_SourceProof_f0d7366f281cd44e7eb0e371
-- name    : SourceProof_f0d7366f281cd44e7eb0e371
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:45:54.146074+00:00
-- url     : https://prove2.me/theorems/6f5766dd-8ab1-5003-adaf-c32ab3cbc750
-- title:
--   StochLean source theorem: StochLean.IsAdmissiblePartitionSequence.restrict_mesh_tendsto

import Definitions.Def_StochLean_Analysis_PathVariation_AdmissiblePartition_F005
import Definitions.Def_SourceProof_b28d937454d2359dad2b7016

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

end LocallyFinitePartition

namespace IsAdmissiblePartitionSequence

theorem _root_.Prove2MeSourceProof.h_f0d7366f281cd44e7eb0e371 {P : ℕ → LocallyFinitePartition}
    (hP : IsAdmissiblePartitionSequence P) (T : ℕ → ℝ≥0) :
    Tendsto (fun n ↦ ((P n).restrict (T n)).mesh) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n ↦ (((P n).restrict (T n)).mesh : ℝ≥0∞)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hP.2
      (fun _ ↦ bot_le) (fun n ↦ (_root_.Prove2MeSourceProof.h_b28d937454d2359dad2b7016 (P n)) (T n))
  exact ENNReal.tendsto_coe.mp hlim
end IsAdmissiblePartitionSequence

end StochLean


