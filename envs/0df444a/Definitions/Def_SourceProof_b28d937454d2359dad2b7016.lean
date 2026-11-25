-- Prove2me | Definitions.Def_SourceProof_b28d937454d2359dad2b7016
-- name    : SourceProof_b28d937454d2359dad2b7016
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:41:32.345554+00:00
-- url     : https://prove2.me/theorems/7ba5a856-af4f-54ea-8111-ff8f936dfb9c
-- title:
--   StochLean source theorem: StochLean.LocallyFinitePartition.restrict_mesh_le

import Definitions.Def_StochLean_Analysis_PathVariation_AdmissiblePartition_F004

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

theorem _root_.Prove2MeSourceProof.h_b28d937454d2359dad2b7016 (P : LocallyFinitePartition) (T : ℝ≥0) :
    ((P.restrict T).mesh : ℝ≥0∞) ≤ P.mesh := by
  exact le_iSup (fun S : ℝ≥0 ↦ ((P.restrict S).mesh : ℝ≥0∞)) T
end LocallyFinitePartition

end StochLean


