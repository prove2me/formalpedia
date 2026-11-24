-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_TotalVariation_F000
-- name    : StochLean_Analysis_PathVariation_TotalVariation_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:19:41.469178+00:00
-- url     : https://prove2.me/theorems/47dbb5ef-e76e-47cc-a5b4-d14a32bddb23
-- title:
--   StochLean: Analysis.PathVariation.TotalVariation F000

import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F000
import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F002
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Total variation and refinement

Klenke 21.60: the one-variation sums increase under refinement and tend to the
canonical Mathlib total variation, which may be infinite. The limit theorem is
stronger than the source nested-partition statement: continuity and vanishing
mesh suffice. Finiteness is required before any conversion to a real number.
-/

@[expose] public section

open Filter Finset Set
open scoped NNReal ENNReal Topology

namespace StochLean

variable {T : ℝ≥0}

/-- Refinement is inclusion of endpoint sets, independent of their chosen enumeration. -/
def TimePartition.Refines (π ρ : TimePartition T) : Prop :=
  Set.range ρ.point ⊆ Set.range π.point
end StochLean


