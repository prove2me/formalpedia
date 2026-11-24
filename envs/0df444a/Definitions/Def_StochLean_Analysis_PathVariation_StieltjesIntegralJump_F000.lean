-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegralJump_F000
-- name    : StochLean_Analysis_PathVariation_StieltjesIntegralJump_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T13:34:03.546407+00:00
-- url     : https://prove2.me/theorems/392c572e-98ca-4302-938c-73a8fb88ec8a
-- title:
--   StochLean: Analysis.PathVariation.StieltjesIntegralJump F000

import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Bases
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Jumps of pathwise Stieltjes integrals at positive times

The source time-zero convention is dealt with separately at the process layer.
Positive-time jumps are obtained from actual atoms of the two component measures.
-/

@[expose] public section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

private theorem leftLim_const_add_sub {p q : ℝ≥0 → ℝ} {t : ℝ≥0}
    (ht : 0 < t) (c : ℝ)
    (hp : Tendsto p (𝓝[<] t) (𝓝 (Function.leftLim p t)))
    (hq : Tendsto q (𝓝[<] t) (𝓝 (Function.leftLim q t))) :
    Function.leftLim (fun u ↦ c + p u - q u) t =
      c + Function.leftLim p t - Function.leftLim q t := by
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  exact leftLim_eq_of_tendsto ((tendsto_const_nhds.add hp).sub hq)
variable {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t} {f : ℝ≥0 → ℝ}

end StochLean


