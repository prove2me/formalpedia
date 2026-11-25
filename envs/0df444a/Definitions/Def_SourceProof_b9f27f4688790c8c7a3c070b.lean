-- Prove2me | Definitions.Def_SourceProof_b9f27f4688790c8c7a3c070b
-- name    : SourceProof_b9f27f4688790c8c7a3c070b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:31:36.804796+00:00
-- url     : https://prove2.me/theorems/67dafe81-4380-5477-bdf5-853161417b73
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.clamp

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F002
import Definitions.Def_SourceProof_3f363a7f74dc18c6b2d72139
import Definitions.Def_SourceProof_c1502d54d2b7490012bf0be0
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.WithTop

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Bounded simple approximation with the original bound

Scalar interval projection fixes zero, so it preserves the full source simple
class. Its nonexpansiveness retains UCP convergence. The input bound may hold
only on one full-measure path event; every approximant is bounded everywhere.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ}

namespace IsSimplePredictable
theorem _root_.Prove2MeSourceProof.h_b9f27f4688790c8c7a3c070b (hH : IsSimplePredictable H F) (C : ℝ≥0) :
    IsSimplePredictable (fun t ω ↦ max (-(C : ℝ)) (min (C : ℝ) (H t ω))) F := by
  exact (_root_.Prove2MeSourceProof.h_3f363a7f74dc18c6b2d72139 hH) (_root_.Prove2MeSourceProof.h_c1502d54d2b7490012bf0be0 F) (fun x _ ↦ max (-(C : ℝ)) (min (C : ℝ) x))
    (measurable_const.max (measurable_const.min measurable_fst))
    (by simp only [min_eq_right C.coe_nonneg, max_eq_right (neg_nonpos.mpr C.coe_nonneg)])
end IsSimplePredictable

end ProbabilityTheory


