-- Prove2me | Definitions.Def_SourceProof_cdf76879721d1dc6620e7985
-- name    : SourceProof_cdf76879721d1dc6620e7985
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:00:33.564337+00:00
-- url     : https://prove2.me/theorems/912dc477-61ef-4fe2-95c0-ab6a5311315c
-- title:
--   StochLean source theorem: StochLean.stieltjesMeasure_real_singleton

import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Bases
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Jumps of pathwise Stieltjes integrals at positive times

The source time-zero convention is dealt with separately at the process layer.
Positive-time jumps are obtained from actual atoms of the two component measures.
-/

@[expose] public section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_cdf76879721d1dc6620e7985 (A : StieltjesFunction ℝ≥0) (t : ℝ≥0) :
    (A.measure {t}).toReal = A t - Function.leftLim A t := by
  rw [StieltjesFunction.measure_singleton,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (A.mono.leftLim_le le_rfl))]
variable {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t} {f : ℝ≥0 → ℝ}

end StochLean


