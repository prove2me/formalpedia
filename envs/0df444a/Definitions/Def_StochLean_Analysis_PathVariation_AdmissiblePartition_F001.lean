-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_AdmissiblePartition_F001
-- name    : StochLean_Analysis_PathVariation_AdmissiblePartition_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:01:53.840736+00:00
-- url     : https://prove2.me/theorems/f2004d89-17de-57a1-9fcb-fd6a9dbd42d5
-- title:
--   StochLean: Analysis.PathVariation.AdmissiblePartition F001

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F002
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F003
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F005
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.Instances.ENNReal.Lemmas

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

/-- Endpoint data of a locally finite partition of the whole nonnegative line. -/
structure LocallyFinitePartition where
  points : Set ℝ≥0
  zero_mem : 0 ∈ points
  finite_bounded : ∀ T, (points ∩ Icc 0 T).Finite
  unbounded : ¬ BddAbove points
namespace LocallyFinitePartition

end LocallyFinitePartition

end StochLean


