-- Prove2me | Definitions.Def_SourceProof_4a2b6d179f277c4abb605f93
-- name    : SourceProof_4a2b6d179f277c4abb605f93
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:34:13.605709+00:00
-- url     : https://prove2.me/theorems/942b8156-b545-5c0d-a31d-7a8f28f95ca1
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPoissonProcess.quadraticVariation_real_eq_of_semimartingale

import Definitions.Def_StochLean_Analysis_PathVariation_UniformPartition_F001
import Definitions.Def_StochLean_Probability_Process_Partition_SquareSums_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_F000
import Definitions.Def_SourceProof_1b5811523ebf232c3a8b514f
import Definitions.Def_SourceProof_25b6fcf830b722c0e0c94355
import Definitions.Def_SourceProof_36da4c661fc115cbdc2bfff4
import Definitions.Def_SourceProof_51c0da11e7e46e13ea7b46dd
import Definitions.Def_SourceProof_5abd8ef5abbb365343c607a9
import Definitions.Def_SourceProof_6ec6ed103d98506e37900b2a
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_c3a38a53524388b4ac4c79ee
import Definitions.Def_SourceProof_cd1d484cf4840a0b4c579db3
import Definitions.Def_SourceProof_d0a4533c9dc122ef1fd7f577
import Definitions.Def_SourceProof_f0d7366f281cd44e7eb0e371
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.UniformSpace.UniformApproximation

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The canonical Poisson and compensated-Poisson brackets

The actual raw square bracket is identified by uniqueness of the square-sum
probability limit. Subtracting the continuous finite-variation drift leaves it
unchanged. All identities hold on one event for all times.
-/

@[expose] public section

open MeasureTheory Filter StochLean
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

namespace IsPoissonProcess
theorem _root_.Prove2MeSourceProof.h_4a2b6d179f277c4abb605f93
    (hN : IsPoissonProcess N rate P)
    (hS : IsSemimartingale (fun t ω ↦ (N t ω : ℝ)) F P) (hF : F.IsUsual P) :
    Indistinguishable (hS.quadraticVariation hF) (fun t ω ↦ (N t ω : ℝ)) P := by
  let π : ℕ → ProbabilityTheory.StoppingTimePartition F := fun n ↦ ProbabilityTheory.StoppingTimePartition.deterministic F
    ((StochLean.LocallyFinitePartition.dyadic n).restrict n)
  have hπ : ProbabilityTheory.StoppingTimePartition.IsTendingToIdentity π P :=
    _root_.Prove2MeSourceProof.h_6ec6ed103d98506e37900b2a
      _root_.Prove2MeSourceProof.h_36da4c661fc115cbdc2bfff4 tendsto_natCast_atTop_atTop
  apply _root_.Prove2MeSourceProof.h_1b5811523ebf232c3a8b514f _
    (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_51c0da11e7e46e13ea7b46dd hS) hF))
    (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c (_root_.Prove2MeSourceProof.h_5abd8ef5abbb365343c607a9 hN))
  intro t
  apply tendstoInMeasure_ae_unique
    ((_root_.Prove2MeSourceProof.h_d0a4533c9dc122ef1fd7f577 ((_root_.Prove2MeSourceProof.h_c3a38a53524388b4ac4c79ee hS) hF hπ)) t)
  have hm := (_root_.Prove2MeSourceProof.h_f0d7366f281cd44e7eb0e371 _root_.Prove2MeSourceProof.h_36da4c661fc115cbdc2bfff4) (fun _ ↦ t)
  have hn := (_root_.Prove2MeSourceProof.h_25b6fcf830b722c0e0c94355 hN)
    (NNReal.continuous_coe.tendsto 0 |>.comp hm)
  refine TendstoInMeasure.congr' ?_ (Filter.Eventually.of_forall fun _ ↦ rfl) hn
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ≥0))
    atTop atTop).eventually (eventually_ge_atTop t)] with n hnt
  filter_upwards [hN.initial] with ω h0
  change StochLean.quadraticVariationSum ((StochLean.LocallyFinitePartition.dyadic n).restrict t)
    (fun s ↦ (N s ω : ℝ)) = (N 0 ω : ℝ) ^ 2 +
      StochLean.quadraticVariationSum ((StochLean.LocallyFinitePartition.dyadic n).restrict n)
        (fun s ↦ (N (min s t) ω : ℝ))
  rw [h0, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
  exact (_root_.Prove2MeSourceProof.h_cd1d484cf4840a0b4c579db3 (StochLean.LocallyFinitePartition.dyadic n)) hnt
    (fun s ↦ (N s ω : ℝ))
end IsPoissonProcess

end ProbabilityTheory


