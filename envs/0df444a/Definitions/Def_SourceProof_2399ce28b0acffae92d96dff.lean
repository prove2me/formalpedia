-- Prove2me | Definitions.Def_SourceProof_2399ce28b0acffae92d96dff
-- name    : SourceProof_2399ce28b0acffae92d96dff
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-26T07:24:18.211776+00:00
-- url     : https://prove2.me/theorems/c17bf0af-0b06-4199-8a68-1f5f980e0a4d
-- title:
--   StochLean source theorem: ProbabilityTheory.IsComplexSemimartingale.differentiable_comp

import Definitions.Def_StochLean_ForMathlib_Analysis_ComplexCoordinateDerivatives_F000
import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_Complex_Basic_F000
import Definitions.Def_SourceProof_41ef9eff4cc7c102f0e2f53b
import Definitions.Def_SourceProof_6d7c45bf5ff46012e47ca9f3
import Definitions.Def_SourceProof_ba881db1353595b7bf417d1e
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Continuity
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
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
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
import Mathlib.Order.Filter.Finite
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
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real
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

/-! # Analytic transformations preserve complex coordinate semimartingales

The argument applies the proved real finite-coordinate C2 theorem to the
actual real and imaginary components. No independent complex stochastic
calculus is assumed in proving preservation.
-/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal

namespace ProbabilityTheory

namespace IsComplexSemimartingale
theorem _root_.Prove2MeSourceProof.h_2399ce28b0acffae92d96dff
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {Z : ℝ≥0 → Ω → ℂ} {f : ℂ → ℂ}
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P) (hf : Differentiable ℂ f) :
    IsComplexSemimartingale (fun t ω ↦ f (Z t ω)) F P := by
  let X : Fin 2 → ℝ≥0 → Ω → ℝ := ![fun t ω ↦ (Z t ω).re, fun t ω ↦ (Z t ω).im]
  have hX : ∀ i, ProbabilityTheory.IsSemimartingale (X i) F P := by
    intro i
    fin_cases i
    · exact hZ.1
    · exact hZ.2
  have he (t : ℝ≥0) (ω : Ω) : StochLean.complexCoordinates (fun i ↦ X i t ω) = Z t ω := by
    apply Complex.ext <;> simp [X]
  constructor
  · simpa only [he, Complex.reCLM_apply] using
      _root_.Prove2MeSourceProof.h_41ef9eff4cc7c102f0e2f53b hX hF
        (_root_.Prove2MeSourceProof.h_ba881db1353595b7bf417d1e hf Complex.reCLM)
  · simpa only [he, Complex.imCLM_apply] using
      _root_.Prove2MeSourceProof.h_41ef9eff4cc7c102f0e2f53b hX hF
        (_root_.Prove2MeSourceProof.h_ba881db1353595b7bf417d1e hf Complex.imCLM)
end IsComplexSemimartingale

end ProbabilityTheory


