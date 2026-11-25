-- Prove2me | Definitions.Def_SourceProof_ca371899a004561914a59371
-- name    : SourceProof_ca371899a004561914a59371
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:46:18.774809+00:00
-- url     : https://prove2.me/theorems/c2d458e2-700f-4302-a96c-e3c29705fcad
-- title:
--   StochLean source theorem: StochLean.quadraticVariationSum_eq_square_sub_leftSum

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F005
import Definitions.Def_SourceProof_e1f3ecca529106853c30fa13
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

/-! # Square sums of a cadlag finite-variation path

The limit is the Stieltjes increment integral of the actual jump. The next
identification with a jump series is separate; no summability is assumed here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace StochLean

variable {T : ℝ≥0} {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t}

theorem _root_.Prove2MeSourceProof.h_ca371899a004561914a59371 (π : TimePartition T) (x : ℝ≥0 → ℝ) :
    quadraticVariationSum π x = x T ^ 2 - x 0 ^ 2 -
      2 * ∑ i : Fin π.size, x (π.left i) * π.increment x i := by
  rw [← (_root_.Prove2MeSourceProof.h_e1f3ecca529106853c30fa13 π) (fun u ↦ x u ^ 2), Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [StochLean.TimePartition.increment]
  ring
end StochLean


