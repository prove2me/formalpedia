-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_Graph_F000
-- name    : StochLean_Probability_Process_Stopping_Graph_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:52.597264+00:00
-- url     : https://prove2.me/theorems/47ef99da-2320-423a-abbc-e537493c3011
-- title:
--   StochLean: Probability.Process.Stopping.Graph F000

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite-time graphs of stopping times

Protter III.2 includes time zero in a stopping-time graph and excludes infinity.
The strict-future region is predictable, the closed-future region is optional,
and every stopping-time graph is optional. Predictability of the graph is not
asserted for an arbitrary stopping time.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

/-- The graph on finite time times sample space; it has no point at infinity. -/
def stoppingTimeGraph {Ω : Type*} (τ : Ω → WithTop ℝ≥0) : Set (ℝ≥0 × Ω) :=
  {p | τ p.2 = (p.1 : WithTop ℝ≥0)}
end ProbabilityTheory

namespace MeasureTheory.IsStoppingTime

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0}

end MeasureTheory.IsStoppingTime


