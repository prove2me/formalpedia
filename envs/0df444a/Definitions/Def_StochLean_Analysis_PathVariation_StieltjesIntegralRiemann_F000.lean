-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegralRiemann_F000
-- name    : StochLean_Analysis_PathVariation_StieltjesIntegralRiemann_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:00:44.283137+00:00
-- url     : https://prove2.me/theorems/e14798a3-e7fc-4f8f-a32b-439bf96c6a17
-- title:
--   StochLean: Analysis.PathVariation.StieltjesIntegralRiemann F000

import Definitions.Def_StochLean_Analysis_PathVariation_LeftStepApproximation_F000
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.Order.LeftRight

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Left Riemann sums for pathwise Stieltjes integrals

The partial terminal cell is included, and the initial term is retained. Uniform
convergence holds on the whole horizon for continuous integrands, even when the
locally BV integrator has jumps. No nested-partition hypothesis is needed.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped NNReal Topology

namespace StochLean

variable {T : ℝ≥0}

noncomputable def stieltjesLeftSum (π : TimePartition T) (x f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  f 0 * x 0 + ∑ i : Fin π.size,
    f (π.left i) * (x (min (π.right i) t) - x (min (π.left i) t))
variable {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t}

end StochLean


