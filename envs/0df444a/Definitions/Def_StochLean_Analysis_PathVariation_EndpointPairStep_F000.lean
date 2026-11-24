-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_EndpointPairStep_F000
-- name    : StochLean_Analysis_PathVariation_EndpointPairStep_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:02:02.692818+00:00
-- url     : https://prove2.me/theorems/26717c4c-53aa-4a88-b561-6fb048b032fd
-- title:
--   StochLean: Analysis.PathVariation.EndpointPairStep F000

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F000
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

/-! # Finite steps depending on both cell endpoint values

Repeated endpoints are allowed. At positive times the unique nonempty cell
determines both values; the initial value is retained separately.
-/

@[expose] public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

namespace TimePartition

variable {T : ℝ≥0} {E : Type*}

noncomputable def endpointPairStep (π : TimePartition T) (Φ : E → E → ℝ)
    (x : ℝ≥0 → E) (t : ℝ≥0) : ℝ :=
  if t = 0 then Φ (x 0) (x 0) else
    ∑ i : Fin π.size, (Ioc (π.left i) (π.right i)).indicator
      (fun _ ↦ Φ (x (π.left i)) (x (π.right i))) t
end TimePartition

variable {T : ℝ≥0} {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t}

end StochLean


