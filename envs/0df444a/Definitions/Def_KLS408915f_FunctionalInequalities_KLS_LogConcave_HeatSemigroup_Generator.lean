-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
-- name    : KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:26:44.342986+00:00
-- url     : https://prove2.me/theorems/a47c5921-7d88-42d9-a720-87c410bc51a2
-- title:
--   Generator identities for smooth compactly supported tests
-- statement:
--   Assume a log-concave probability law satisfies $\nu=m.\operatorname{tilted}(-U)$ for a $C^1$ potential $U$. The theorem `integral_inner_gradient_eq` states that for $f\in C_c^2(V)$ and $g\in C^1(V)$, $\int\langle\nabla f,\nabla g\rangle\,d\nu=\int(-\mathcal L_Uf)g\,d\nu$, where `weightedLaplacian` is $\mathcal L_U$. For $f\in C_c^\infty(V)$, the bundle establishes square-integrability of $\nabla f$ and $-\mathcal L_Uf$, membership of $[f]$ in the domain of the closed gradient and its adjoint composition, and the corresponding weak identity; `closedWeightedOperator_toLp_eq` identifies the closed gradient of $[f]$ with $[\nabla f]$.
-- source:
--   Source: Klartag–Lehec, Bourgain’s slicing problem and KLS isoperimetry up to polylog (arXiv:2203.15551v2), item E14. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Generator.lean#L59-L198 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator`, definition bundle `KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointClosure
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Contraction
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_MeanValue
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Form
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_VonNeumann
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Limit
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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Closure
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
import Mathlib.Analysis.Calculus.Deriv.MeanValue
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
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
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
import Mathlib.Analysis.SpecialFunctions.Exponential
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
open MeasureTheory FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff LinearPMap RealInnerProductSpace
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
open Energy Energy.WeightedGradient
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section Tilted
variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
include hνU hU in
omit [SecondCountableTopology V] in
/-- **weighted integration by parts, weighted integration by parts for the law `ν = m.tilted (-U)`**: for a `C²` compactly
supported `f` and a `C¹` function `g`, `∫ ⟪∇f, ∇g⟫ dν = ∫ (-ℒf) g dν`. -/
theorem integral_inner_gradient_eq {f g : V → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 1 g) :
    ∫ x, ⟪gradient f x, gradient g x⟫ ∂(ν : Measure V) =
      ∫ x, -weightedLaplacian U f x * g x ∂(ν : Measure V) := by
  rw [hνU]
  exact integral_inner_gradient_tilted m hU hf hfc hg
end Tilted
section Generator
variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
omit [FiniteDimensional ℝ V] in
/-- The gradient of a smooth compactly supported function is square integrable for every
probability law. -/
theorem memLp_gradient_of_contDiff_hasCompactSupport {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) : MemLp (gradient f) 2 (ν : Measure V) := by
  simpa only [apply_id] using
    (IsTest.of_contDiff_hasCompactSupport ν (ContinuousLinearMap.id ℝ V) hf hfc).memLp_apply
omit [SecondCountableTopology V] in
/-- `-ℒ f ∈ L²(ν)` for `f ∈ C_c^∞(V)` and a `C¹` potential: the integrability clause of the smooth-test generator identity. -/
theorem memLp_neg_weightedLaplacian (hU : ContDiff ℝ 1 U) {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    MemLp (fun x => -weightedLaplacian U f x) 2 (ν : Measure V) :=
  (memLp_weightedLaplacian hU (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hfc 2).neg
/-- The class of a smooth compactly supported function lies in the domain of the closed
unit-weight gradient. -/
theorem toLp_mem_closedWeightedOperator_domain {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    (memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain :=
  (LinearPMap.le_closure _).1
    (toLp_mem_domain_operator ν (ContinuousLinearMap.id ℝ V) _
      (IsTest.of_contDiff_hasCompactSupport ν _ hf hfc))
/-- The closed unit-weight gradient sends the class of a smooth compactly supported function to
the class of its gradient. -/
theorem closedWeightedOperator_toLp_eq {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩ =
      (memLp_gradient_of_contDiff_hasCompactSupport hf hfc).toLp (gradient f) := by
  have htest := IsTest.of_contDiff_hasCompactSupport ν (ContinuousLinearMap.id ℝ V) hf hfc
  have hmem := toLp_mem_domain_operator ν (ContinuousLinearMap.id ℝ V)
    (hν.absolutelyContinuous_haar m hi) htest
  rw [← (LinearPMap.le_closure (hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi)).2
    (x := ⟨_, hmem⟩) (y := ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩) rfl,
    operator_apply ν (ContinuousLinearMap.id ℝ V) _ (hν.frontier_support_eq_zero hi) htest hmem rfl]
  exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun y => by rw [apply_id])
include hνU hU in
/-- **The weak identity on the domain of `T̄`**: for `f ∈ C_c^∞(V)` and every `x ∈ D(T̄)`,
`⟪[-ℒf], x⟫ = ⟪[∇f], T̄ x⟫` in `L²(ν)`. On smooth compactly supported classes this is weighted integration by parts; it
extends to `D(T̄)` because those classes are a graph-norm core of `T̄`. -/
theorem inner_toLp_neg_weightedLaplacian_eq {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f)
    (x : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    ⟪(memLp_neg_weightedLaplacian (ν := ν) hU hf hfc).toLp (fun y => -weightedLaplacian U f y),
        (x : Lp ℝ 2 (ν : Measure V))⟫ =
      ⟪(memLp_gradient_of_contDiff_hasCompactSupport hf hfc).toLp (gradient f),
        hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi x⟫ := by
  have hSclos : ((hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi).domRestrict
      (smoothCore ν)).closure = hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi :=
    hν.closure_domRestrict_eq_of_smoothCore_le m (ContinuousLinearMap.id ℝ V) hi le_rfl
      (smoothCore_le_domain_operator ν (ContinuousLinearMap.id ℝ V) _)
  have hSc : ((hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi).domRestrict
      (smoothCore ν)).IsClosable :=
    (hν.weightedOperator_isClosable m (ContinuousLinearMap.id ℝ V) hi).leIsClosable
      LinearPMap.domRestrict_le
  have hcore : ∀ y : ((hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi).domRestrict
      (smoothCore ν)).domain,
      ⟪(memLp_neg_weightedLaplacian (ν := ν) hU hf hfc).toLp (fun y => -weightedLaplacian U f y),
        (y : Lp ℝ 2 (ν : Measure V))⟫ =
      ⟪(memLp_gradient_of_contDiff_hasCompactSupport hf hfc).toLp (gradient f),
        (hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi).domRestrict (smoothCore ν) y⟫ := by
    rintro ⟨y, hy⟩
    have hy1 : y ∈ smoothCore ν := (Submodule.mem_inf.mp hy).1
    have hy2 : y ∈ (hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain :=
      (Submodule.mem_inf.mp hy).2
    obtain ⟨g, hg, hgc, rfl⟩ := hy1
    have htest := IsTest.of_contDiff_hasCompactSupport ν (ContinuousLinearMap.id ℝ V) hg hgc
    have hSy : (hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi).domRestrict (smoothCore ν)
        ⟨_, hy⟩ = htest.memLp_apply.toLp (apply (ContinuousLinearMap.id ℝ V) g) := by
      erw [LinearPMap.domRestrict_apply (x := ⟨_, hy⟩) (y := ⟨_, hy2⟩) rfl]
      exact operator_apply ν (ContinuousLinearMap.id ℝ V) _ (hν.frontier_support_eq_zero hi) htest
        hy2 rfl
    rw [hSy, L2.inner_def, L2.inner_def]
    have h1 : (fun a => ⟪((memLp_neg_weightedLaplacian (ν := ν) hU hf hfc).toLp
          (fun y => -weightedLaplacian U f y) : Lp ℝ 2 (ν : Measure V)) a,
          ((memLp_of_contDiff_hasCompactSupport ν hg hgc).toLp g : Lp ℝ 2 (ν : Measure V)) a⟫)
        =ᵐ[(ν : Measure V)] fun a => -weightedLaplacian U f a * g a := by
      filter_upwards [(memLp_neg_weightedLaplacian (ν := ν) hU hf hfc).coeFn_toLp,
        (memLp_of_contDiff_hasCompactSupport ν hg hgc).coeFn_toLp] with a ha hb
      rw [ha, hb, Real.inner_apply]
    have h2 : (fun a => ⟪((memLp_gradient_of_contDiff_hasCompactSupport hf hfc).toLp (gradient f) :
          Lp V 2 (ν : Measure V)) a,
          (htest.memLp_apply.toLp (apply (ContinuousLinearMap.id ℝ V) g) :
            Lp V 2 (ν : Measure V)) a⟫)
        =ᵐ[(ν : Measure V)] fun a => ⟪gradient f a, gradient g a⟫ := by
      filter_upwards [(memLp_gradient_of_contDiff_hasCompactSupport hf hfc).coeFn_toLp,
        htest.memLp_apply.coeFn_toLp] with a ha hb
      rw [ha, hb, apply_id]
    rw [integral_congr_ae h1, integral_congr_ae h2]
    exact (integral_inner_gradient_eq m hνU hU (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hfc
      (hg.of_le (WithTop.coe_le_coe.mpr le_top))).symm
  have := inner_eq_inner_closure_apply hSc hcore
  rw [hSclos] at this
  exact this x
include hνU hU in
/-- **the smooth-test generator identity, domain clause**: for `f ∈ C_c^∞(V)`, the class `[f]` lies in `D(T̄†T̄)`. -/
theorem toLp_mem_adjointComp_domain {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    (memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f ∈
      (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain := by
  have hD := hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc
  refine ⟨mem_adjointCompDomain.mpr ⟨hD, ?_⟩, hD⟩
  rw [hν.closedWeightedOperator_toLp_eq m hi hf hfc]
  exact LinearPMap.mem_adjoint_domain_of_exists _
    ⟨_, fun x => hν.inner_toLp_neg_weightedLaplacian_eq m hi hνU hU hf hfc x⟩
end Generator
end LogConcave
end KLS
end FunctionalInequalities


