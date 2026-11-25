-- Prove2me | Definitions.Def_SourceProof_4a1642646798190188bdf9ea
-- name    : SourceProof_4a1642646798190188bdf9ea
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:30:48.780959+00:00
-- url     : https://prove2.me/theorems/ffeeca34-008f-4e2a-a042-beca3e583152
-- title:
--   StochLean source theorem: StochLean.normSquarePairSum_stop_terminal

import Definitions.Def_StochLean_Analysis_PathVariation_VectorPairSums_F000
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

theorem _root_.Prove2MeSourceProof.h_4a1642646798190188bdf9ea {S T : ℝ≥0} (π : TimePartition S) (hT : T ≤ S)
    (Φ : E → E → ℝ) (x : ℝ≥0 → E) :
    normSquarePairSum (π.stop T hT) Φ x T = normSquarePairSum π Φ x T := by
  simp only [StochLean.normSquarePairSum, StochLean.TimePartition.left, StochLean.TimePartition.right, StochLean.TimePartition.stop,
    min_assoc, min_self]
  rfl
end StochLean


