-- Prove2me | Definitions.Def_SourceProof_7f5f06ceb9dbdad2c95df667
-- name    : SourceProof_7f5f06ceb9dbdad2c95df667
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:38:38.476051+00:00
-- url     : https://prove2.me/theorems/33180ced-a13b-561e-bf59-5095917a5999
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPoissonProcess.quadraticVariation_real_eq

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_F000
import Definitions.Def_SourceProof_4a2b6d179f277c4abb605f93
import Definitions.Def_SourceProof_879467c9061f5f7e3a779f57
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
import Mathlib.Data.Finset.Sort
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
import Mathlib.Topology.Instances.ENNReal.Lemmas
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
theorem _root_.Prove2MeSourceProof.h_7f5f06ceb9dbdad2c95df667
    (hN : IsPoissonProcess N rate P) (hF : F.IsUsual P) (ha : Adapted F N) :
    Indistinguishable (((_root_.Prove2MeSourceProof.h_879467c9061f5f7e3a779f57 hN) hF ha).quadraticVariation hF)
      (fun t ω ↦ (N t ω : ℝ)) P :=
  (_root_.Prove2MeSourceProof.h_4a2b6d179f277c4abb605f93 hN) ((_root_.Prove2MeSourceProof.h_879467c9061f5f7e3a779f57 hN) hF ha) hF
end IsPoissonProcess

end ProbabilityTheory


