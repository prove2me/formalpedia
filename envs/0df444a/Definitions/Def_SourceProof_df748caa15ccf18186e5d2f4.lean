-- Prove2me | Definitions.Def_SourceProof_df748caa15ccf18186e5d2f4
-- name    : SourceProof_df748caa15ccf18186e5d2f4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:09.210877+00:00
-- url     : https://prove2.me/theorems/8d73d45a-c315-523e-a55e-37fbb88f8957
-- title:
--   StochLean source theorem: StochLean.pathStieltjesIncrementIntegral_sub

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegral_F000
import Definitions.Def_SourceProof_0e9a3c1ecba0183e8cff41a4
import Definitions.Def_SourceProof_17e97db7cf70e0ac4580327f
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Max
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.IsLUB
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

theorem _root_.Prove2MeSourceProof.h_df748caa15ccf18186e5d2f4 {f g : ℝ≥0 → ℝ} {s t : ℝ≥0}
    (hf : IntegrableOn f (Ioc s t) (totalVariationStieltjes x hx hr).measure)
    (hg : IntegrableOn g (Ioc s t) (totalVariationStieltjes x hx hr).measure) :
    pathStieltjesIncrementIntegral x hx hr (fun u ↦ f u - g u) s t =
      pathStieltjesIncrementIntegral x hx hr f s t -
        pathStieltjesIncrementIntegral x hx hr g s t := by
  simp only [StochLean.pathStieltjesIncrementIntegral,
    integral_sub (_root_.Prove2MeSourceProof.h_17e97db7cf70e0ac4580327f hf)
      (_root_.Prove2MeSourceProof.h_17e97db7cf70e0ac4580327f hg),
    integral_sub (_root_.Prove2MeSourceProof.h_0e9a3c1ecba0183e8cff41a4 hf)
      (_root_.Prove2MeSourceProof.h_0e9a3c1ecba0183e8cff41a4 hg)]
  ring
end StochLean


