-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_LinearEquiv
-- name    : KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_LinearEquiv
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:35:58.215396+00:00
-- url     : https://prove2.me/theorems/f77b1a0d-d596-4b5f-a3f5-7a4eaa0357b0
-- title:
--   Linear-equivalence transport of covariance-gradient tests
-- statement:
--   `Euclidean.gradient_comp_continuousLinearEquiv` states that the gradient of $g\circ T$ is $T^*\nabla g\circ T$ for a continuous linear equivalence T, without a differentiability premise. `CovarianceGradient.Test.compContinuousLinearEquiv` transports a covariance-gradient test through a measure-preserving T when the covariance quadratic forms satisfy $\langle\operatorname{Cov}(\nu_2)w,w\rangle=\langle\operatorname{Cov}(\nu_1)T^*w,T^*w\rangle$. The transported test includes the corresponding Lipschitz, $L^2$, and covariance-gradient integrability conditions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/CovarianceGradient/LinearEquiv.lean#L48-L100 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.CovarianceGradient.LinearEquiv`, definition bundle `KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_LinearEquiv`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Translation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
namespace FunctionalInequalities
namespace Energy
open Energy.Euclidean
universe u v
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [CompleteSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [CompleteSpace V₂]
section Gradient
namespace Euclidean
/-- The gradient of a function composed with a continuous linear equivalence is the adjoint image
of the gradient at the image point. No differentiability premise is needed. -/
theorem gradient_comp_continuousLinearEquiv (g : V₂ → ℝ) (T : V₁ ≃L[ℝ] V₂) (x : V₁) :
    gradient (fun y ↦ g (T y)) x = (T : V₁ →L[ℝ] V₂).adjoint (gradient g (T x)) := by
  apply (toDual ℝ V₁).injective
  rw [toDual_gradient]
  have hcomp : fderiv ℝ (fun y ↦ g (T y)) x = (fderiv ℝ g (T x)).comp (T : V₁ →L[ℝ] V₂) := by
    have h := T.comp_right_fderiv (f := g) (x := x)
    simpa only [Function.comp_def] using h
  rw [hcomp]
  ext v
  change fderiv ℝ g (T x) (T v) = inner ℝ ((T : V₁ →L[ℝ] V₂).adjoint (gradient g (T x))) v
  rw [← toDual_gradient, toDual_apply_apply, ContinuousLinearMap.adjoint_inner_left]
  rfl
end Euclidean
end Gradient
section Tests
variable [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁] [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂] [FiniteDimensional ℝ V₂]
variable {ν₁ : ProbabilityMeasure V₁} {ν₂ : ProbabilityMeasure V₂} {T : V₁ ≃L[ℝ] V₂}
namespace CovarianceGradient
namespace Test
/-- Composition of a covariance test with a measure-preserving continuous linear equivalence
between two laws whose covariance quadratic forms correspond under the adjoint. -/
def compContinuousLinearEquiv
    (hmp : MeasurePreserving T (ν₁ : Measure V₁) (ν₂ : Measure V₂))
    (hcov : ∀ w, inner ℝ (Covariance.operator (ν₂ : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν₁ : Measure V₁) ((T : V₁ →L[ℝ] V₂).adjoint w))
        ((T : V₁ →L[ℝ] V₂).adjoint w))
    (g : Test ν₂) : Test ν₁ where
  toFun := fun x ↦ g (T x)
  lipschitz := by
    obtain ⟨K, hK⟩ := g.lipschitz
    exact ⟨K * ‖(T : V₁ →L[ℝ] V₂)‖₊, hK.comp (T : V₁ →L[ℝ] V₂).lipschitz⟩
  memLp_two := by
    have := g.memLp_two
    rw [← hmp.map_eq] at this
    exact (memLp_map_measure_iff (hmp.map_eq ▸ g.memLp_two.1) hmp.aemeasurable).mp this
  integrable := by
    have hdens : density ν₁ (fun x ↦ g (T x)) =
        density ν₂ g.toFun ∘ T := by
      funext x
      simp only [density, Function.comp_apply,
        gradient_comp_continuousLinearEquiv, hcov]
    rw [hdens]
    have := g.integrable
    rw [← hmp.map_eq] at this
    exact (integrable_map_measure (hmp.map_eq ▸ g.integrable.1) hmp.aemeasurable).mp this
end Test
end CovarianceGradient
end Tests
end Energy
end FunctionalInequalities


