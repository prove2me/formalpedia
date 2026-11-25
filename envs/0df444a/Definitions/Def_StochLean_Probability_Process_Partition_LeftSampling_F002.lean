-- Prove2me | Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F002
-- name    : StochLean_Probability_Process_Partition_LeftSampling_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:29.094719+00:00
-- url     : https://prove2.me/theorems/5da1b9c9-6416-4fc9-8648-c21dd11950e5
-- title:
--   StochLean: Probability.Process.Partition.LeftSampling F002

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Probability.Process.Predictable
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Left sampling and increment-only Riemann sums on random partitions

The sampled process reuses the deterministic left-step owner pathwise. Its
initial value is the original initial value. The Riemann sum, in contrast,
contains only increments, so its formula subtracts the source initial product.
Repeated endpoints and arbitrary finite stopping endpoints remain legal.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

def leftRiemannSumProcess (π : StoppingTimePartition F) (Y X : ℝ≥0 → Ω → ℝ) :
    ℝ≥0 → Ω → ℝ := fun t ω ↦ ∑ i : Fin π.size,
      Y (π.point i.castSucc ω) ω *
        (X (min (π.point i.succ ω) t) ω - X (min (π.point i.castSucc ω) t) ω)
end ProbabilityTheory.StoppingTimePartition


