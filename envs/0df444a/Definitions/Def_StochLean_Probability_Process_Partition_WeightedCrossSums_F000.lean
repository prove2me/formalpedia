-- Prove2me | Definitions.Def_StochLean_Probability_Process_Partition_WeightedCrossSums_F000
-- name    : StochLean_Probability_Process_Partition_WeightedCrossSums_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:17:18.501094+00:00
-- url     : https://prove2.me/theorems/ea8d08f1-e61a-4318-b940-14f42840d781
-- title:
--   StochLean: Probability.Process.Partition.WeightedCrossSums F000

import Definitions.Def_StochLean_Probability_Process_Partition_F000
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Probability.Process.Predictable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Bases
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual weighted mixed increment sums

Weights are sampled at the original left endpoints. The moving partial cell
is retained, and zero-length cells are allowed. These increment sums have no
initial atom, unlike the raw mixed bracket itself.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

def weightedQuadraticCovariationSumProcess (π : StoppingTimePartition F)
    (H X Y : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t ω ↦
  ∑ i : Fin π.size, H (π.point i.castSucc ω) ω *
    (X (min (π.point i.succ ω) t) ω - X (min (π.point i.castSucc ω) t) ω) *
    (Y (min (π.point i.succ ω) t) ω - Y (min (π.point i.castSucc ω) t) ω)
end ProbabilityTheory.StoppingTimePartition


