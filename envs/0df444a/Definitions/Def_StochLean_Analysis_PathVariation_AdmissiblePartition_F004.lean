-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_AdmissiblePartition_F004
-- name    : StochLean_Analysis_PathVariation_AdmissiblePartition_F004
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:36:36.64233+00:00
-- url     : https://prove2.me/theorems/eee089a9-f08e-44bc-9593-9ec285c82334
-- title:
--   StochLean: Analysis.PathVariation.AdmissiblePartition F004

import Definitions.Def_StochLean_Analysis_PathVariation_AdmissiblePartition_F003

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

/-- Extended maximum adjacent gap over all finite horizons. No finiteness fallback is used. -/
noncomputable def mesh (P : LocallyFinitePartition) : ℝ≥0∞ :=
  ⨆ T : ℝ≥0, ((P.restrict T).mesh : ℝ≥0∞)
end LocallyFinitePartition

end StochLean


