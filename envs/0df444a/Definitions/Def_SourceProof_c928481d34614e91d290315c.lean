-- Prove2me | Definitions.Def_SourceProof_c928481d34614e91d290315c
-- name    : SourceProof_c928481d34614e91d290315c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:47:07.35074+00:00
-- url     : https://prove2.me/theorems/e543e29a-09ad-4ef4-8916-a1154fc8f81c
-- title:
--   StochLean source theorem: StochLean.integrableOn_variationStieltjes_taggedStep

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegralRiemann_F000
import Definitions.Def_StochLean_Analysis_PathVariation_TaggedStepApproximation_F000
import Definitions.Def_SourceProof_0b9fe09b8f4623735111204a
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

theorem _root_.Prove2MeSourceProof.h_c928481d34614e91d290315c (π : TimePartition T)
    (ξ : Fin π.size → ℝ≥0) (f : ℝ≥0 → ℝ) (t : ℝ≥0) :
    IntegrableOn (π.taggedStep ξ f) (Ioc 0 t) (totalVariationStieltjes x hx hr).measure :=
  _root_.Prove2MeSourceProof.h_0b9fe09b8f4623735111204a π.left π.right (fun i ↦ f (ξ i)) (f 0) t
end StochLean


