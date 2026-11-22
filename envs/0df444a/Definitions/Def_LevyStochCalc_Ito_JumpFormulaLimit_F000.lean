-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaLimit_F000
-- name    : LevyStochCalc_Ito_JumpFormulaLimit_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:33:15.441105+00:00
-- url     : https://prove2.me/theorems/33392291-5bf7-4601-89ec-856085d74a5e
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaLimit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaLimit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityDrift_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityExhaustion_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityExhaustion_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityExhaustion_F002
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F002
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.FiniteExhaustion
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.PiSystem
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
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.CompactSystem
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.EMetricSpace.PairReduction
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.IsClosedRestrict
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Topology.MetricSpace.MetricSeparated
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The small-jump limit of the Itô–Lévy formula

The finite-activity Itô–Lévy formula applies to a jump diffusion whose jump coefficient is cut to
a set of marks. Along a family `A : ℕ → Set E` of small-jump sets with `ν`-null intersection the
cut coefficients restore the original ones, and the formula is passed to the limit term by term:
the increment of the state function and the drift, diffusion and compensated jump terms converge
along the truncated paths, and the compensator-drift term converges by dominated convergence on
the product of the time window with the intensity. The identity of the limits is then the
uniqueness of the limit of a real sequence, read on the two sides of the formula.

Cutting the jump coefficient to a set of marks leaves the drift integrand `∂_t u + 𝓛u` unchanged
— it reads only `μ` and `σ` — and turns the compensator-drift integrand into its restriction to
that set. The two presentations of the drift differ by the first-order term `∑ᵢ ∂ᵢu ∫ γᵢ dν`,
which is finite only when the jump coefficient is `ν`-integrable: for a jump coefficient that is
merely square-integrable near the small marks, the first-order term and the mark integral of the
jump increment `u(x + γ) − u(x)` each diverge and only their difference, the compensator-drift
integrand `u(x + γ) − u(x) − γᵀ∇u`, is integrable. The limit statements below are therefore
carried by the compensator-drift integrand; the first-order term is passed to the limit
separately only under an integrability hypothesis on the jump coefficient itself.

## Main definitions

* `LevyStochCalc.Ito.JumpFormula.markTruncCoeffs` — the coefficient bundle with the jump
  coefficient cut to a set of marks.
* `LevyStochCalc.Ito.JumpFormula.firstOrderIntegrand` — the first-order term `∑ᵢ γᵢ ∂ᵢu` of the
  compensator-drift integrand.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.ae_eventually_notMem_of_antitone`,
  `LevyStochCalc.Ito.JumpFormula.ae_eventually_notMem_comp` — almost every mark eventually lies
  outside an antitone family of mark sets with null intersection, also along a subsequence.
* `LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_of_dominated` — dominated convergence for
  the mark integral over the complements of the family, integrated over a time window.
* `LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_compensatorDrift` — the compensator-drift
  integrals over the complements of the family converge to the compensator-drift integral over
  the whole mark space along the limit path.
* `LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_firstOrder` — the same for the first-order
  term, under integrability of the jump coefficient against the intensity.
* `LevyStochCalc.Ito.JumpFormula.driftIntegrand_markTruncCoeffs`,
  `LevyStochCalc.Ito.JumpFormula.integral_compensatorDriftIntegrand_markTruncCoeffs` — cutting
  the jump coefficient leaves the drift integrand unchanged and restricts the compensator-drift
  integral to the cut.
* `LevyStochCalc.Ito.JumpFormula.itoLevy_sub_of_markTruncCoeffs` — the Itô–Lévy identity for cut
  coefficients, in the vocabulary of the uncut ones.
* `LevyStochCalc.Ito.JumpFormula.itoLevy_of_tendsto`,
  `LevyStochCalc.Ito.JumpFormula.ae_itoLevy_of_ae_tendsto` — the two sides of an identity of
  real sequences have equal limits, pointwise and almost surely.
* `LevyStochCalc.Ito.JumpFormula.ae_itoLevy_of_ae_tendsto_terms` — the Itô–Lévy identity along
  the limit path, from the identities along the truncated paths with the drift and
  compensator-drift terms given as arbitrary sequences, and the convergence of the five terms.
* `LevyStochCalc.Ito.JumpFormula.ae_itoLevy_of_ae_tendsto_integrals` — the same with the drift
  and compensator-drift terms given as the integrals along the truncated paths, the latter over
  the complements of the truncated mark sets.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., 2009, Theorem 4.4.7, step (II).
-/

open MeasureTheory Filter Topology
open LevyStochCalc.Ito.Setting

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section MarkSets

variable {E : Type v} [MeasurableSpace E] {ν : Measure E}

/-- Along an antitone family of mark sets whose intersection is `ν`-null, almost every mark lies
outside all but finitely many members of the family. -/
theorem ae_eventually_notMem_of_antitone {A : ℕ → Set E} (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) : ∀ᵐ e ∂ν, ∀ᶠ m in atTop, e ∉ A m := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with e he
  simp only [Set.mem_iInter, not_forall] at he
  obtain ⟨m₀, hm₀⟩ := he
  filter_upwards [eventually_ge_atTop m₀] with m hm
  exact fun hcon => hm₀ (hanti hm hcon)
/-- Reading an antitone family of mark sets with `ν`-null intersection along an index map that
dominates the identity keeps almost every mark eventually outside the family. -/
theorem ae_eventually_notMem_comp {A : ℕ → Set E} (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) {ms : ℕ → ℕ} (hms : ∀ k, k ≤ ms k) :
    ∀ᵐ e ∂ν, ∀ᶠ k in atTop, e ∉ A (ms k) := by
  filter_upwards [ae_eventually_notMem_of_antitone hanti hnull] with e he
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp he
  filter_upwards [eventually_ge_atTop m₀] with k hk
  exact hm₀ (ms k) (le_trans hk (hms k))
end MarkSets

section Dominated

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

end Dominated

section Continuity

variable {n : ℕ} {E : Type v} {u : ℝ → (Fin n → ℝ) → ℝ}
  {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)}

end Continuity

section CompensatorDriftLimit

variable {n : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  {u : ℝ → (Fin n → ℝ) → ℝ} {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)}

end CompensatorDriftLimit

section MarkTruncation

variable {n d : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ}

end MarkTruncation

section Assembly

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

end Assembly

end LevyStochCalc.Ito.JumpFormula


