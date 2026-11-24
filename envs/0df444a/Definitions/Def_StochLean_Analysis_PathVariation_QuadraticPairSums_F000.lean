-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_QuadraticPairSums_F000
-- name    : StochLean_Analysis_PathVariation_QuadraticPairSums_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:02:08.447271+00:00
-- url     : https://prove2.me/theorems/97481d2b-3e7f-4d6f-b935-6a44f73e1131
-- title:
--   StochLean: Analysis.PathVariation.QuadraticPairSums F000

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F000
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Data.Finset.Max
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Quadratic endpoint-pair sums and vanishing continuous diagonal errors

The last partially traversed cell is included. Uniform control needs a bound
on the actual partial square sums, not monotonicity of those sums in time.
-/

@[expose] public section

open Filter Set Finset
open scoped NNReal Topology

namespace StochLean

noncomputable def quadraticPairSum {S : ℝ≥0} (π : TimePartition S)
    (Φ : ℝ → ℝ → ℝ) (x : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  ∑ i : Fin π.size,
    Φ (x (min (π.left i) t)) (x (min (π.right i) t)) *
      (x (min (π.right i) t) - x (min (π.left i) t)) ^ 2
end StochLean


