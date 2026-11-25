-- Prove2me | Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F001
-- name    : StochLean_Probability_Process_Partition_LeftSampling_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:25:33.50626+00:00
-- url     : https://prove2.me/theorems/f045302e-f8e7-4bb5-a269-09448e0528ca
-- title:
--   StochLean: Probability.Process.Partition.LeftSampling F001

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

noncomputable def leftSampleRep (π : StoppingTimePartition F) (Y : ℝ≥0 → Ω → ℝ)
    (h0 : Measurable[F 0] (Y 0))
    (hcoef : ∀ i : Fin π.size,
      Measurable[(π.point i.castSucc).measurableSpace] (fun ω ↦ Y (π.point i.castSucc ω) ω)) :
    SimplePredictableRep F where
  partition := π
  initial := Y 0
  measurable_initial := h0
  coefficient := fun i ω ↦ Y (π.point i.castSucc ω) ω
  measurable_coefficient := hcoef
end ProbabilityTheory.StoppingTimePartition


