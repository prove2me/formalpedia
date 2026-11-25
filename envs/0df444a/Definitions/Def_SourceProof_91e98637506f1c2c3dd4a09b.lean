-- Prove2me | Definitions.Def_SourceProof_91e98637506f1c2c3dd4a09b
-- name    : SourceProof_91e98637506f1c2c3dd4a09b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T22:09:20.192846+00:00
-- url     : https://prove2.me/theorems/9aaa7564-3297-5eb3-b185-d16535ef374a
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.hasFiniteVariationPaths_contDiff_second_order_jump_remainders

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_FiniteVariation_F000
import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_SourceProof_41299065cd79548c26fd1d4d
import Definitions.Def_SourceProof_578f0da3aeb916476fab77ac
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Group.Basic
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
import Mathlib.Topology.Order.Basic
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

/-! # Finite variation of both actual Ito jump-correction processes -/

@[expose] public section

open MeasureTheory Set StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {f : ℝ → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_91e98637506f1c2c3dd4a09b
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 2 f) :
    HasFiniteVariationPaths (fun t ω ↦ ∑' s : Ioc 0 t,
      (f (X s ω) - f (leftLimitProcess X s ω) -
        deriv f (leftLimitProcess X s ω) * jumpProcess X s ω -
        deriv (deriv f) (leftLimitProcess X s ω) / 2 * (jumpProcess X s ω) ^ 2)) P := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_578f0da3aeb916476fab77ac hX) hF hf] with ω hs
  exact _root_.Prove2MeSourceProof.h_41299065cd79548c26fd1d4d
    (g := fun s ↦ f (X s ω) - f (ProbabilityTheory.leftLimitProcess X s ω) -
      deriv f (ProbabilityTheory.leftLimitProcess X s ω) * ProbabilityTheory.jumpProcess X s ω -
      deriv (deriv f) (ProbabilityTheory.leftLimitProcess X s ω) / 2 * (ProbabilityTheory.jumpProcess X s ω) ^ 2) hs
end IsSemimartingale

end ProbabilityTheory


