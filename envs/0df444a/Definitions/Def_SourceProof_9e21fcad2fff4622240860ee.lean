-- Prove2me | Definitions.Def_SourceProof_9e21fcad2fff4622240860ee
-- name    : SourceProof_9e21fcad2fff4622240860ee
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:02:34.21639+00:00
-- url     : https://prove2.me/theorems/fe7ecf0d-4fd2-4a1d-b61e-de136cf36f98
-- title:
--   StochLean source theorem: StochLean.pathStieltjesIncrementIntegral_leftStep_terminal

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegralRiemann_F000
import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegral_F000
import Definitions.Def_SourceProof_7571e2c33b7245dcac603c85
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stieltjes endpoint sums for cadlag integrands

Dominated convergence uses the actual total-variation measure on a finite
horizon. Left sums converge to the strict-left integrand and right sums to
the original integrand. These are increment integrals, without an initial atom.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace StochLean

variable {T : ℝ≥0} {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t}

theorem _root_.Prove2MeSourceProof.h_9e21fcad2fff4622240860ee (π : TimePartition T)
    (f : ℝ≥0 → ℝ) :
    pathStieltjesIncrementIntegral x hx hr (π.leftStep f) 0 T =
      ∑ i : Fin π.size, f (π.left i) * π.increment x i :=
  _root_.Prove2MeSourceProof.h_7571e2c33b7245dcac603c85 π π.left f
end StochLean


