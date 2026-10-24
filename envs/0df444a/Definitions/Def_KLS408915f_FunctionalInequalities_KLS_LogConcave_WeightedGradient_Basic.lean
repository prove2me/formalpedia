-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
-- name    : KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:43:40.497541+00:00
-- url     : https://prove2.me/theorems/fb7e8b54-85f9-4187-8b60-887821e3b30c
-- title:
--   Weighted gradient operator for full-dimensional log-concave laws
-- statement:
--   For a log-concave probability law ν whose support has nonempty interior, `LogConcave.absolutelyContinuous_haar` gives absolute continuity with respect to any additive Haar measure, `frontier_support_eq_zero` gives ν-nullity of the support frontier, and `locallyDominates` gives local domination on compact subsets of the support interior. `weightedOperator` is the weighted-gradient operator built from this absolute continuity. The declarations `weightedOperator_isClosable` and `dense_domain_weightedOperator` state that this operator is closable and densely defined, and `closure_domRestrict_eq_of_smoothCore_le` gives the same closure for every core lying between the smooth core and the operator domain. No Poincaré inequality or KLS bound is asserted.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Basic.lean#L50-L119 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Basic`, definition bundle `KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Closable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
open Energy Energy.Euclidean Probability
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section FullDimensional
variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
omit [CompleteSpace V] in
/-- A full-dimensional log-concave law is absolutely continuous with respect to Haar measure. -/
theorem absolutelyContinuous_haar (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) : (ν : Measure V) ≪ m :=
  hν.absolutelyContinuous_of_interior_support_nonempty m hi
omit [CompleteSpace V] in
/-- The frontier of the convex support of a full-dimensional log-concave law is null. -/
theorem frontier_support_eq_zero (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    (ν : Measure V) (frontier (ν : Measure V).support) = 0 :=
  hν.absolutelyContinuous_haar Measure.addHaar hi
    (hν.convex_support.addHaar_frontier Measure.addHaar)
omit [CompleteSpace V] in
/-- On compact subsets of the support interior the Borell density is bounded below by a positive
constant, so Haar measure is locally dominated by the law. -/
theorem locallyDominates (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) : LocallyDominates ν m := by
  obtain ⟨ρ, hρ⟩ := hν.exists_isBorellDensity_of_interior_support_nonempty m hi
    (hν.absolutelyContinuous_haar m hi)
  intro K hK hKΩ
  obtain ⟨a, b, ha, hab⟩ := hρ.exists_bounds_of_isCompact hK hKΩ
  set a' : ℝ≥0 := Real.toNNReal a with ha'
  have ha'0 : a' ≠ 0 := (Real.toNNReal_pos.mpr ha).ne'
  refine ⟨a'⁻¹, Measure.le_iff.mpr fun s hs ↦ ?_⟩
  rw [Measure.smul_apply, Measure.restrict_apply hs, Measure.restrict_apply hs, smul_eq_mul,
    ENNReal.coe_inv ha'0]
  have hν' : (ν : Measure V) (s ∩ K) = ∫⁻ x in s ∩ K, ENNReal.ofReal (ρ x) ∂m := by
    rw [← hρ.withDensity_eq, withDensity_apply _ (hs.inter hK.measurableSet)]
  have hlow : (a' : ℝ≥0∞) * m (s ∩ K) ≤ (ν : Measure V) (s ∩ K) := by
    rw [hν', ← setLIntegral_const]
    refine setLIntegral_mono hρ.measurable.ennreal_ofReal fun x hx ↦ ?_
    exact ENNReal.ofReal_le_ofReal (hab x hx.2).1
  have ha'top : (a' : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have ha'0' : (a' : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha'0
  calc m (s ∩ K) = ((a' : ℝ≥0∞))⁻¹ * ((a' : ℝ≥0∞) * m (s ∩ K)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha'0' ha'top, one_mul]
    _ ≤ ((a' : ℝ≥0∞))⁻¹ * (ν : Measure V) (s ∩ K) := by gcongr
variable (B : V →L[ℝ] V)
/-- The weighted gradient operator of a full-dimensional log-concave law. -/
abbrev weightedOperator (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V) :=
  Energy.WeightedGradient.operator ν B (hν.absolutelyContinuous_haar m hi)
/-- Closability on a full-dimensional log-concave law. -/
theorem weightedOperator_isClosable (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    (hν.weightedOperator m B hi).IsClosable :=
  Energy.WeightedGradient.operator_isClosable ν B _ (hν.frontier_support_eq_zero hi)
    (hν.locallyDominates m hi)
/-- Dense domain on a full-dimensional log-concave law. -/
theorem dense_domain_weightedOperator (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    Dense ((hν.weightedOperator m B hi).domain : Set (Lp ℝ 2 (ν : Measure V))) :=
  Energy.WeightedGradient.dense_domain_operator ν B _
/-- Every core between the smooth compactly supported classes and the full domain has the same
closure as the operator; the Blueprint's `ℝ + C_c^∞(V)` is such a core. -/
theorem closure_domRestrict_eq_of_smoothCore_le (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty)
    {S : Submodule ℝ (Lp ℝ 2 (ν : Measure V))} (hS : Energy.WeightedGradient.smoothCore ν ≤ S)
    (hS' : S ≤ (hν.weightedOperator m B hi).domain) :
    ((hν.weightedOperator m B hi).domRestrict S).closure = (hν.weightedOperator m B hi).closure :=
  Energy.WeightedGradient.closure_domRestrict_eq_of_smoothCore_le ν B _
    (hν.frontier_support_eq_zero hi) (hν.weightedOperator_isClosable m B hi) hS hS'
end FullDimensional
end LogConcave
end KLS
end FunctionalInequalities


