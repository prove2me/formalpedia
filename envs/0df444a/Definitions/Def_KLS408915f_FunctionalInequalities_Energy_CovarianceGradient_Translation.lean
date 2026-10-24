-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Translation
-- name    : KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Translation
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:35:17.51171+00:00
-- url     : https://prove2.me/theorems/6ec79f40-1d2c-4205-ab05-a42f707a28b7
-- title:
--   Translation of covariance-gradient tests
-- statement:
--   `Euclidean.gradient_comp_const_add` identifies the gradient of $y\mapsto g(c+y)$ with the translated gradient, and `lipschitzWith_const_add` records that translation is 1-Lipschitz. `CovarianceGradient.Test.translate` composes a covariance-gradient test for ν₂ with $x\mapsto c+x$ to obtain a test for ν₁, assuming the translation is measure-preserving and the covariance operators are equal. The resulting statement includes the required Lipschitz, $L^2$, and integrability fields but does not itself assert equality of relaxation constants.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/CovarianceGradient/Translation.lean#L40-L82 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.CovarianceGradient.Translation`, definition bundle `KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Translation`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
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
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
section Tests
namespace Euclidean
/-- The gradient of a translated function is the translated gradient. -/
theorem gradient_comp_const_add (g : V → ℝ) (c x : V) :
    gradient (fun y ↦ g (c + y)) x = gradient g (c + x) := by
  apply (toDual ℝ V).injective
  simp only [toDual_gradient]
  exact fderiv_comp_add_left c
omit [InnerProductSpace ℝ V] [CompleteSpace V] in
/-- Translations are `1`-Lipschitz. -/
theorem lipschitzWith_const_add (c : V) : LipschitzWith 1 (fun x : V ↦ c + x) :=
  LipschitzWith.of_dist_le_mul fun x y ↦ by simp [dist_eq_norm]
end Euclidean
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable {ν₁ ν₂ : ProbabilityMeasure V} {c : V}
namespace CovarianceGradient
namespace Test
/-- Composition of a covariance test with a measure-preserving translation between two laws with
the same covariance operator. -/
def translate
    (hmp : MeasurePreserving (fun x ↦ c + x) (ν₁ : Measure V) (ν₂ : Measure V))
    (hcov : Covariance.operator (ν₂ : Measure V) = Covariance.operator (ν₁ : Measure V))
    (g : Test ν₂) : Test ν₁ where
  toFun := fun x ↦ g (c + x)
  lipschitz := by
    obtain ⟨K, hK⟩ := g.lipschitz
    exact ⟨K * 1, hK.comp (lipschitzWith_const_add c)⟩
  memLp_two := by
    have := g.memLp_two
    rw [← hmp.map_eq] at this
    exact (memLp_map_measure_iff (hmp.map_eq ▸ g.memLp_two.1) hmp.aemeasurable).mp this
  integrable := by
    have hdens : density ν₁ (fun x ↦ g (c + x)) =
        density ν₂ g.toFun ∘ fun x ↦ c + x := by
      funext x
      simp only [density, Function.comp_apply, gradient_comp_const_add, hcov]
    rw [hdens]
    have := g.integrable
    rw [← hmp.map_eq] at this
    exact (integrable_map_measure (hmp.map_eq ▸ g.integrable.1) hmp.aemeasurable).mp this
end Test
end CovarianceGradient
end Tests
end Energy
end FunctionalInequalities


