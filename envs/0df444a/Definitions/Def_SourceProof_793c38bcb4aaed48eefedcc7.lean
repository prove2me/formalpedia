-- Prove2me | Definitions.Def_SourceProof_793c38bcb4aaed48eefedcc7
-- name    : SourceProof_793c38bcb4aaed48eefedcc7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:52.847522+00:00
-- url     : https://prove2.me/theorems/65530538-a05e-44d8-826c-5b95193b90b8
-- title:
--   StochLean source theorem: ProbabilityTheory.clamp_eq_of_norm_le

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F002
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

theorem _root_.Prove2MeSourceProof.h_793c38bcb4aaed48eefedcc7 {C : ℝ≥0} {x : ℝ} (hx : ‖x‖ ≤ C) :
    max (-(C : ℝ)) (min (C : ℝ) x) = x := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp (show |x| ≤ C from hx)
  rw [min_eq_right hhi, max_eq_right hlo]
end ProbabilityTheory


