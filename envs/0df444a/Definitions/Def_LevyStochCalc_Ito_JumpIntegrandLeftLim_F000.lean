-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpIntegrandLeftLim_F000
-- name    : LevyStochCalc_Ito_JumpIntegrandLeftLim_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:00:28.189204+00:00
-- url     : https://prove2.me/theorems/5611062c-f2af-43b9-9b23-552c26f14196
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpIntegrandLeftLim
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpIntegrandLeftLim. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_CadlagJumps_F000
import Definitions.Def_LevyStochCalc_Analysis_CadlagJumps_F001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.FiniteExhaustion
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Order.CompleteLattice.Group
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Martingale.Upcrossing
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Notation
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.CompactSystem
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.EMetricSpace.PairReduction
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.IsClosedRestrict
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Topology.MetricSpace.MetricSeparated
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Separation.Regular

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Integrands evaluated along the left limits of a path

A path in `ℝⁿ` that is right continuous on `[0, ∞)` and has left limits at every positive time
meets those left limits off a countable, hence Lebesgue null, set of times. An integrand
evaluated along such a path and the same integrand evaluated along a process that meets the path
at all but countably many positive times therefore agree almost everywhere for the product of the
sample measure, Lebesgue measure on the horizon and the mark measure, so the compensated integral
takes the same value on the two integrands; the same null set serves the iterated integral
against the mark measure and Lebesgue measure and the integral against the reference intensity.

The identification is one of `L²` classes: it concerns the compensated integral constructed from
the energy isometry, not a pathwise Stieltjes integral against the jump measure, for which the
two conventions differ.

## Main statements

* `countable_setOf_pos_ne_of_cadlag` — a path right continuous on `[0, ∞)` differs from its left
  limits at only countably many positive times.
* `compensatedIntegral_congr_of_countable_ne` — the compensated integrals of an integrand
  evaluated along two processes meeting at all but countably many positive times agree almost
  surely.
* `setIntegral_congr_of_countable_ne` and
  `setIntegral_referenceIntensity_congr_of_countable_ne` — the same for the compensator drift
  term, in its iterated and its product-measure form.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito

universe u v w

section Cadlag

variable {n : ℕ}

/-- The times at which a path in `ℝⁿ` that is right continuous with left limits differs from its
left limits form a countable set. -/
theorem countable_setOf_ne_leftLim_pi {f : ℝ → Fin n → ℝ}
    (hright : ∀ t : ℝ, Tendsto f (𝓝[>] t) (𝓝 (f t)))
    (hleft : ∀ (t : ℝ) (i : Fin n), ∃ L : ℝ, Tendsto (fun s => f s i) (𝓝[<] t) (𝓝 L)) :
    {t : ℝ | f t ≠ fun i => Function.leftLim (fun s => f s i) t}.Countable := by
  have hsub : {t : ℝ | f t ≠ fun i => Function.leftLim (fun s => f s i) t}
      ⊆ ⋃ i : Fin n, {t : ℝ | f t i ≠ Function.leftLim (fun s => f s i) t} := by
    intro t ht
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hcon
    exact ht (funext fun i => not_not.mp fun hi => hcon ⟨i, hi⟩)
  refine Set.Countable.mono hsub (Set.countable_iUnion fun i => ?_)
  exact _root_.Prove2MeSourceProof.h_471832330986c475a11444b3
    (fun t => (hright t).apply_nhds i) (fun t => hleft t i)
end Cadlag

section Horizon

end Horizon

section Integrand

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {V : Type w}
  {P : Measure Ω}

end Integrand

section Compensated

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {V : Type w}
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

end Compensated

section Drift

variable {Ω : Type u} {E : Type v} [MeasurableSpace E] {V : Type w}

end Drift

end LevyStochCalc.Ito


