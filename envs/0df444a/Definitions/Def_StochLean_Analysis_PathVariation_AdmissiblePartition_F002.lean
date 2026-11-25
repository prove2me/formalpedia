-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_AdmissiblePartition_F002
-- name    : StochLean_Analysis_PathVariation_AdmissiblePartition_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:10:00.238867+00:00
-- url     : https://prove2.me/theorems/dc569f5d-fa06-43e5-815b-4072c38e4e42
-- title:
--   StochLean: Analysis.PathVariation.AdmissiblePartition F002

import Definitions.Def_StochLean_Analysis_PathVariation_AdmissiblePartition_F001

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

noncomputable def restrictFinset (P : LocallyFinitePartition) (T : ℝ≥0) : Finset ℝ≥0 :=
  insert T (P.finite_bounded T).toFinset
end LocallyFinitePartition

end StochLean


