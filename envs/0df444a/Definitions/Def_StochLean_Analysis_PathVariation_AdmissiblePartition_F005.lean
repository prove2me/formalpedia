-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_AdmissiblePartition_F005
-- name    : StochLean_Analysis_PathVariation_AdmissiblePartition_F005
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:41:02.859547+00:00
-- url     : https://prove2.me/theorems/2f9c369b-0fbe-4629-8329-65290d818e61
-- title:
--   StochLean: Analysis.PathVariation.AdmissiblePartition F005

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

end LocallyFinitePartition

/-- Corrected Klenke admissibility: nested sets and vanishing maximum adjacent gap.
No summable mesh rate or prescribed refinement ratio is imposed. -/
def IsAdmissiblePartitionSequence (P : ℕ → LocallyFinitePartition) : Prop :=
  Monotone (fun n ↦ (P n).points) ∧ Tendsto (fun n ↦ (P n).mesh) atTop (𝓝 0)
end StochLean


