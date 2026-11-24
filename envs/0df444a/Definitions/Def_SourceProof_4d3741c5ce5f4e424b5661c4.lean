-- Prove2me | Definitions.Def_SourceProof_4d3741c5ce5f4e424b5661c4
-- name    : SourceProof_4d3741c5ce5f4e424b5661c4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:13:49.203094+00:00
-- url     : https://prove2.me/theorems/bc74b3db-2519-45e6-bb64-94d35b3c8931
-- title:
--   StochLean source theorem: StochLean.TimePartition.measurable_taggedStep

import Definitions.Def_StochLean_Analysis_PathVariation_TaggedStepApproximation_F000
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Endpoint step convergence at jumps

On positive-time cells the left endpoint approaches strictly from below,
while the right endpoint approaches from above, allowing equality. Thus the
limits are different at jumps. No uniform convergence is asserted.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0} {π : ℕ → TimePartition T} {f : ℝ≥0 → ℝ}

theorem _root_.Prove2MeSourceProof.h_4d3741c5ce5f4e424b5661c4 (π : TimePartition T) (ξ : Fin π.size → ℝ≥0)
    (f : ℝ≥0 → ℝ) : Measurable (π.taggedStep ξ f) := by
  classical
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (Finset.measurable_sum _ fun _ _ ↦ measurable_const.indicator measurableSet_Ioc)
end StochLean.TimePartition


