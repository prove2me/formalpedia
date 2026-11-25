-- Prove2me | Definitions.Def_SourceProof_868765551567206b826f381b
-- name    : SourceProof_868765551567206b826f381b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:31:25.518306+00:00
-- url     : https://prove2.me/theorems/25180f05-67ee-4127-9920-c03ddc1157d0
-- title:
--   StochLean source theorem: StochLean.normSquareVariationSum_stop

import Definitions.Def_StochLean_Analysis_PathVariation_VectorEnergy_F000
import Definitions.Def_SourceProof_939d8318cd36045b63ec8877
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Order.Filter.Finite
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Jump-series convergence for partial quadratic-pair sums

Partition horizons may vary and only need eventually cover the fixed
evaluation time. Clipping retains repeated endpoints and the last partial
cell; no additional mesh rate or refinement assumption is introduced.
-/

@[expose] public section

open Set Finset Filter ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E]

theorem _root_.Prove2MeSourceProof.h_868765551567206b826f381b {S T : ℝ≥0} (π : TimePartition S) (hT : T ≤ S)
    (x : ℝ≥0 → E) : normSquareVariationSum (π.stop T hT) x =
      normSquareVariationSum π (fun u ↦ x (min u T)) := rfl
end StochLean


