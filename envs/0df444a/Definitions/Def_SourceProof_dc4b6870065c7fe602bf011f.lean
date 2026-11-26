-- Prove2me | Definitions.Def_SourceProof_dc4b6870065c7fe602bf011f
-- name    : SourceProof_dc4b6870065c7fe602bf011f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-26T07:20:55.945252+00:00
-- url     : https://prove2.me/theorems/c8cf02b7-4ccb-5afa-8337-70806ad28845
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPoissonProcess.quadraticVariation_compensated_eq

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_F000
import Definitions.Def_SourceProof_00a8a291a5ec377d57feab0f
import Definitions.Def_SourceProof_2c0d4ca99a3f51a9d8eb6cb0
import Definitions.Def_SourceProof_63e1469ea21d6ee826860dba
import Definitions.Def_SourceProof_6ed3c177b9234dc2ab8ed747
import Definitions.Def_SourceProof_76fb0853953befebe1f8862c
import Definitions.Def_SourceProof_7f5f06ceb9dbdad2c95df667
import Definitions.Def_SourceProof_879467c9061f5f7e3a779f57
import Definitions.Def_SourceProof_aecae218d87a3a485c80985f
import Definitions.Def_SourceProof_b1a5ba19b01fd793d7051a6c
import Definitions.Def_SourceProof_cfcbcbe0a1d572b37d51f9a8
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.InfiniteSum
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
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real

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
theorem _root_.Prove2MeSourceProof.h_dc4b6870065c7fe602bf011f
    (hN : IsPoissonProcess N rate P) (hF : F.IsUsual P) (ha : Adapted F N) :
    Indistinguishable (((_root_.Prove2MeSourceProof.h_cfcbcbe0a1d572b37d51f9a8 hN) hF ha).quadraticVariation hF)
      (fun t ω ↦ (N t ω : ℝ)) P := by
  let D : ℝ≥0 → Ω → ℝ := fun t _ ↦ (rate : ℝ) * t
  have hc : ProbabilityTheory.HasContinuousPaths D P := ae_of_all _ fun _ ↦
    NNReal.continuous_coe.const_mul (rate : ℝ)
  have hv : ProbabilityTheory.HasFiniteVariationPaths D P := by
    apply _root_.Prove2MeSourceProof.h_6ed3c177b9234dc2ab8ed747
    exact ae_of_all _ fun _ _ _ h ↦ mul_le_mul_of_nonneg_left
      (NNReal.coe_le_coe.mpr h) rate.2
  have hd : ProbabilityTheory.IsSemimartingale D F P := (_root_.Prove2MeSourceProof.h_00a8a291a5ec377d57feab0f hv) (fun _ ↦ measurable_const)
    hF (_root_.Prove2MeSourceProof.h_2c0d4ca99a3f51a9d8eb6cb0 hc)
  let hS := (_root_.Prove2MeSourceProof.h_879467c9061f5f7e3a779f57 hN) hF ha
  filter_upwards [(_root_.Prove2MeSourceProof.h_76fb0853953befebe1f8862c hS) hd hF, (_root_.Prove2MeSourceProof.h_7f5f06ceb9dbdad2c95df667 hN) hF ha,
    (_root_.Prove2MeSourceProof.h_b1a5ba19b01fd793d7051a6c hS) hd hF hc hv,
    (_root_.Prove2MeSourceProof.h_aecae218d87a3a485c80985f hd) hF hc hv]
    with ω he hq hm hdt t
  change ((_root_.Prove2MeSourceProof.h_63e1469ea21d6ee826860dba hS) hd).quadraticVariation hF t ω = (N t ω : ℝ)
  rw [he t, hq t, hm t, hdt t]
  simp only [D, NNReal.coe_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero,
    add_zero]
end IsPoissonProcess

end ProbabilityTheory


