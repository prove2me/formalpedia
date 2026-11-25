-- Prove2me | Definitions.Def_SourceProof_aecae218d87a3a485c80985f
-- name    : SourceProof_aecae218d87a3a485c80985f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:14:35.466818+00:00
-- url     : https://prove2.me/theorems/2a551034-89fb-5c53-b315-10063840f9f5
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticVariation_of_continuous_finiteVariation

import Definitions.Def_StochLean_Probability_Process_Path_FiniteVariation_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_F000
import Definitions.Def_SourceProof_0c0d0488f9fb511ca3468926
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The raw bracket on continuous finite-variation paths

The assertion is local to sample paths: the finite-variation event need not
have full measure. The initial square remains, even for a nonzero constant.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_aecae218d87a3a485c80985f
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths X P) (hv : HasFiniteVariationPaths X P) :
    Indistinguishable (hX.quadraticVariation hF) (fun _ ω ↦ (X 0 ω) ^ 2) P := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_0c0d0488f9fb511ca3468926 hX) hF, hc, hv]
    with ω h hcω hvω
  exact h hcω hvω
end IsSemimartingale

end ProbabilityTheory


