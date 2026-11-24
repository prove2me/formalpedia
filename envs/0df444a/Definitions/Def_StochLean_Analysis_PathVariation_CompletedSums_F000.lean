-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_CompletedSums_F000
-- name    : StochLean_Analysis_PathVariation_CompletedSums_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T13:11:12.252084+00:00
-- url     : https://prove2.me/theorems/50b660e3-ad9e-4d65-9567-d5a9bd7e016c
-- title:
--   StochLean: Analysis.PathVariation.CompletedSums F000

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Completed-cell variation sums

Completed square sums, unlike sums with a moving partial terminal cell, are
monotone in time. Their covariation analogue has total variation bounded by
the sum of the absolute increment products. This is the deterministic repair
required for Klenke 21.71, and the variation estimate behind Remark 21.61(ii).
-/

@[expose] public section

open Filter Finset Set
open scoped NNReal ENNReal Topology

namespace StochLean

/-- Cumulative sum of finitely many jumps. The event includes the jump time. -/
noncomputable def cumulativeStepSum {ι : Type*} [Fintype ι]
    (a : ι → ℝ≥0) (c : ι → ℝ) (t : ℝ≥0) : ℝ :=
  ∑ i, if a i ≤ t then c i else 0
variable {T : ℝ≥0}

end StochLean


