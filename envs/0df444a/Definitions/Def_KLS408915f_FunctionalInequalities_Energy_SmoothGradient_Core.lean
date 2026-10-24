-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Core
-- name    : KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Core
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:25:16.653015+00:00
-- url     : https://prove2.me/theorems/3bdf22d8-fa17-4e4e-9508-146ab9e1e826
-- title:
--   Local density hypotheses for smooth-gradient cores
-- statement:
--   `SmoothGradient.LocalDensity` records an open set $\Omega\subset V$, a measurable density $\rho$, the fact that $\nu(\Omega^c)=0$, and the identity $\nu|_\Omega=(m|_\Omega)\,\rho$ in `withDensity` form. It also requires $\rho>0$ $m$-almost everywhere on $\Omega$ and an essentially bounded reciprocal on every compact subset of $\Omega$. The theorem `LocalDensity.measure_eq` gives the density integral formula on measurable subsets of $\Omega$, and `LocalDensity.absolutelyContinuous` gives $\nu\ll m$; `lipschitzOperator` is the unit-weight gradient operator and `Test.memLp_gradient` supplies square-integrability of gradients of smooth tests.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/SmoothGradient/Core.lean#L44-L177 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.SmoothGradient.Core`, definition bundle `KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Core`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Closable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
namespace FunctionalInequalities
namespace Energy
namespace SmoothGradient
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
/-- Density hypotheses of the Blueprint: an open set `Ω` carrying `ν` on which `ν` has the
`m`-density `ρ`, positive almost everywhere with locally essentially bounded reciprocal. -/
structure LocalDensity (ν : ProbabilityMeasure V) (m : Measure V) where
  /-- The open set carrying the law. -/
  Ω : Set V
  isOpen : IsOpen Ω
  /-- The density on `Ω`. -/
  ρ : V → ℝ
  measurable : Measurable ρ
  /-- The complement of `Ω` is `ν`-null. -/
  compl_null : (ν : Measure V) Ωᶜ = 0
  /-- On Borel subsets of `Ω`, `ν` integrates `ρ` against `m`. -/
  restrict_eq : (ν : Measure V).restrict Ω =
    (m.restrict Ω).withDensity fun x ↦ ENNReal.ofReal (ρ x)
  /-- The density is positive almost everywhere on `Ω`. -/
  pos : ∀ᵐ x ∂m, x ∈ Ω → 0 < ρ x
  /-- The reciprocal of the density is essentially bounded on compact subsets of `Ω`. -/
  inv_locallyBounded : ∀ K : Set V, IsCompact K → K ⊆ Ω → ∃ C : ℝ, ∀ᵐ x ∂m, x ∈ K → (ρ x)⁻¹ ≤ C
namespace LocalDensity
variable {ν : ProbabilityMeasure V} {m : Measure V} (D : LocalDensity ν m)
omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The law of a measurable subset of `Ω` is the integral of the density. -/
theorem measure_eq {s : Set V} (hs : MeasurableSet s) (hsΩ : s ⊆ D.Ω) :
    (ν : Measure V) s = ∫⁻ x in s, ENNReal.ofReal (D.ρ x) ∂m := by
  have h1 : (ν : Measure V) s = ((ν : Measure V).restrict D.Ω) s := by
    rw [Measure.restrict_apply hs, Set.inter_eq_self_of_subset_left hsΩ]
  rw [h1, D.restrict_eq, withDensity_apply _ hs, Measure.restrict_restrict hs,
    Set.inter_eq_self_of_subset_left hsΩ]
omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
include D in
/-- The law is absolutely continuous with respect to `m`. -/
theorem absolutelyContinuous : (ν : Measure V) ≪ m := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs0 ↦ ?_
  have hsplit := measure_inter_add_sdiff (μ := (ν : Measure V)) s D.isOpen.measurableSet
  have h1 : (ν : Measure V) (s ∩ D.Ω) = 0 := by
    rw [D.measure_eq (hs.inter D.isOpen.measurableSet) Set.inter_subset_right]
    exact setLIntegral_measure_zero _ _ (measure_mono_null Set.inter_subset_left hs0)
  have h2 : (ν : Measure V) (s \ D.Ω) = 0 :=
    measure_mono_null (fun x hx ↦ hx.2) D.compl_null
  rw [← hsplit, h1, h2, add_zero]
variable [m.IsAddHaarMeasure]
end LocalDensity
section Agreement
variable (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure] (D : LocalDensity ν m)
open Energy.WeightedGradient Energy.Euclidean
/-- The unit-weight gradient operator on globally Lipschitz tests, under the density
hypotheses. -/
def lipschitzOperator : Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V) :=
  operator ν (ContinuousLinearMap.id ℝ V) D.absolutelyContinuous
omit [FiniteDimensional ℝ V] in
/-- The gradient of a smooth test is square integrable. -/
theorem Test.memLp_gradient (f : Test ν) : MemLp (gradient f.toFun) 2 (ν : Measure V) :=
  (memLp_two_iff_integrable_sq_norm (LipschitzApproximation.aestronglyMeasurable_gradient _ _)).mpr
    f.gradient_sq_integrable
end Agreement
end SmoothGradient
end Energy
end FunctionalInequalities


