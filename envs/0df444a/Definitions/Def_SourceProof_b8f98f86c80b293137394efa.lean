-- Prove2me | Definitions.Def_SourceProof_b8f98f86c80b293137394efa
-- name    : SourceProof_b8f98f86c80b293137394efa
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:56:41.905623+00:00
-- url     : https://prove2.me/theorems/574e1042-a07e-558e-ac92-bde5b11263bf
-- title:
--   StochLean source theorem: ProbabilityTheory.hasFiniteVariationPaths_frechet_second_order_jump_remainders

import Definitions.Def_StochLean_ForMathlib_Analysis_FrechetTaylorCoefficient_F000
import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_FiniteVariation_F000
import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_SourceProof_41299065cd79548c26fd1d4d
import Definitions.Def_SourceProof_83e0b6f196e4f43fa027ce93
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Probability.Process.Predictable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.WithTop
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.UniformSpace.UniformConvergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite variation of actual vector Ito jump corrections -/

@[expose] public section

open MeasureTheory Set StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
  {X : ι → ℝ≥0 → Ω → ℝ} {f : (ι → ℝ) → ℝ}

theorem _root_.Prove2MeSourceProof.h_b8f98f86c80b293137394efa
    (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 2 f) :
    HasFiniteVariationPaths (fun t ω ↦ ∑' s : Ioc 0 t,
      frechetSecondOrderRemainder f (fun i ↦ leftLimitProcess (X i) s ω)
        (fun i ↦ X i s ω)) P := by
  filter_upwards [_root_.Prove2MeSourceProof.h_83e0b6f196e4f43fa027ce93 hX hF hf] with ω hs
  exact _root_.Prove2MeSourceProof.h_41299065cd79548c26fd1d4d
    (g := fun s ↦ StochLean.frechetSecondOrderRemainder f (fun i ↦ ProbabilityTheory.leftLimitProcess (X i) s ω)
      (fun i ↦ X i s ω)) (fun t ↦ (hs t).2)
end ProbabilityTheory


