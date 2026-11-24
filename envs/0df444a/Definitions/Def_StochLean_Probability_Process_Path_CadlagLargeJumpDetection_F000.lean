-- Prove2me | Definitions.Def_StochLean_Probability_Process_Path_CadlagLargeJumpDetection_F000
-- name    : StochLean_Probability_Process_Path_CadlagLargeJumpDetection_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:48.894373+00:00
-- url     : https://prove2.me/theorems/4cf061d1-09cd-4fa3-b9c2-26f46628b849
-- title:
--   StochLean: Probability.Process.Path.CadlagLargeJumpDetection F000

import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Detecting an actual cadlag jump on a countable grid

A strict large jump in an open time interval is equivalent to arbitrarily
short large increments on one compact internal interval. Both compact
endpoints and the increment samples can be taken from the fixed countable
dense grid; the increment threshold is rational and strictly above the
requested jump threshold. Compact short-window control proves the converse.

In particular this does not treat the generally discontinuous jump process
as a right-continuous process, and makes no stopping-time claim by itself.
-/

@[expose] public section

open Filter Set Metric TopologicalSpace
open scoped NNReal Topology

namespace ProbabilityTheory

/-- Countably many short-increment tests on a fixed compact interval. -/
def HasArbitrarilyShortDenseIncrements (x : ℝ≥0 → ℝ) (a d : ℝ≥0) (c : ℝ) : Prop :=
  ∀ n : ℕ, ∃ i j : ℕ,
    a ≤ denseSeq ℝ≥0 i ∧ denseSeq ℝ≥0 i ≤ denseSeq ℝ≥0 j ∧ denseSeq ℝ≥0 j ≤ d ∧
      dist (denseSeq ℝ≥0 i) (denseSeq ℝ≥0 j) < 1 / (n + 1 : ℝ) ∧
        c < ‖x (denseSeq ℝ≥0 j) - x (denseSeq ℝ≥0 i)‖
variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

end ProbabilityTheory


