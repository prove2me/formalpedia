-- Prove2me | Definitions.Def_SourceProof_a3e9660b6c7c895b0c4c58de
-- name    : SourceProof_a3e9660b6c7c895b0c4c58de
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:17:07.835371+00:00
-- url     : https://prove2.me/theorems/7159fefc-fbb0-55dd-903e-1ab68c7c48be
-- title:
--   StochLean source theorem: StochLean.pathStieltjesIncrementIntegral_chain_rule

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegralRiemann_F000
import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegral_F000
import Definitions.Def_SourceProof_36da4c661fc115cbdc2bfff4
import Definitions.Def_SourceProof_4546bb95a5806728f3a3f870
import Definitions.Def_SourceProof_d1f56c901130ae82276034d4
import Definitions.Def_SourceProof_f0d7366f281cd44e7eb0e371
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # C1 change of variables along a continuous finite-variation path

The first-order remainders are bounded by their derivative oscillation times
the path variation. Actual left Riemann sums identify the Stieltjes integral.
The increment formula excludes the separately owned source initial term.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped NNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_a3e9660b6c7c895b0c4c58de {T : ℝ≥0} {x : ℝ≥0 → ℝ}
    {hv : LocallyBoundedVariationOn x univ} {hr : ∀ t, ContinuousWithinAt x (Ici t) t}
    (hx : ContinuousOn x (Icc 0 T))
    {φ φ' : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ' z) z) (hc : Continuous φ') :
    pathStieltjesIncrementIntegral x hv hr (fun t ↦ φ' (x t)) 0 T = φ (x T) - φ (x 0) := by
  let π : ℕ → StochLean.TimePartition T := fun n ↦ (StochLean.LocallyFinitePartition.dyadic n).restrict T
  have hm : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0) := by
    exact_mod_cast (NNReal.continuous_coe.tendsto 0).comp
      ((_root_.Prove2MeSourceProof.h_f0d7366f281cd44e7eb0e371 _root_.Prove2MeSourceProof.h_36da4c661fc115cbdc2bfff4) (fun _ ↦ T))
  have hfv : BoundedVariationOn x (Icc 0 T) := by
    simpa only [univ_inter] using hv 0 T (mem_univ _) (mem_univ _)
  have hi := _root_.Prove2MeSourceProof.h_d1f56c901130ae82276034d4 (x := x) (hx := hv) (hr := hr)
    (hc.comp_continuousOn hx) hm
  have hs := _root_.Prove2MeSourceProof.h_4546bb95a5806728f3a3f870 hx hfv hφ hc hm
  have heq := tendsto_nhds_unique hi
    ((tendsto_const_nhds (x := φ' (x 0) * x 0)).add hs)
  change φ' (x 0) * x 0 + StochLean.pathStieltjesIncrementIntegral x hv hr (fun t ↦ φ' (x t)) 0 T =
    φ' (x 0) * x 0 + (φ (x T) - φ (x 0)) at heq
  exact add_left_cancel heq
end StochLean


