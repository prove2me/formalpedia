-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Energy_CovarianceGradient_LinearEquiv
-- name    : KLSModular_FunctionalInequalities_Energy_CovarianceGradient_LinearEquiv
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:25:58.713995+00:00
-- url     : https://prove2.me/theorems/3edabcc8-b48c-4028-8b8e-560f716da5f0
-- title:
--   Linear-equivalence transport of covariance-gradient tests
-- statement:
--   `Euclidean.gradient_comp_continuousLinearEquiv` states that the gradient of $g\circ T$ is $T^*\nabla g\circ T$ for a continuous linear equivalence T, without a differentiability premise. `CovarianceGradient.Test.compContinuousLinearEquiv` transports a covariance-gradient test through a measure-preserving T when the covariance quadratic forms satisfy $\langle\operatorname{Cov}(\nu_2)w,w\rangle=\langle\operatorname{Cov}(\nu_1)T^*w,T^*w\rangle$. The transported test includes the corresponding Lipschitz, $L^2$, and covariance-gradient integrability conditions.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.L2.Transport
--   import FunctionalInequalities.Energy.CovarianceGradient.Isometry
--   import FunctionalInequalities.Energy.CovarianceGradient.Translation
--   import Mathlib.Analysis.InnerProductSpace.Adjoint
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   def compContinuousLinearEquiv
--       (hmp : MeasurePreserving T (ν₁ : Measure V₁) (ν₂ : Measure V₂))
--       (hcov : ∀ w, inner ℝ (Covariance.operator (ν₂ : Measure V₂) w) w =
--         inner ℝ (Covariance.operator (ν₁ : Measure V₁) ((T : V₁ →L[ℝ] V₂).adjoint w))
--           ((T : V₁ →L[ℝ] V₂).adjoint w))
--       (g : Test ν₂) : Test ν₁
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`L2/Transport`](https://prove2.me/theorems/18833b5b-77e3-4a08-986b-55e8c2b513b7), [`Energy/CovarianceGradient/Isometry`](https://prove2.me/theorems/cdf6b1ca-48ee-4055-8d41-f18529ef0dcb), [`Energy/CovarianceGradient/Translation`](https://prove2.me/theorems/707a03ec-125b-44b1-be52-91f91946c0fb).
--
--   Theorems in source order:
--
--   - [`relaxation_mapContinuousLinearEquiv`](https://prove2.me/theorems/57355011-3577-4382-8bb8-e203da4929a1)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/CovarianceGradient/LinearEquiv.lean) · `FunctionalInequalities.Energy.CovarianceGradient.LinearEquiv` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/CovarianceGradient/LinearEquiv.lean#L48-L100 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.CovarianceGradient.LinearEquiv`, definition bundle `KLSModular_FunctionalInequalities_Energy_CovarianceGradient_LinearEquiv`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_L2_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_CovarianceGradient_Isometry
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_CovarianceGradient_Translation
import Mathlib.Analysis.InnerProductSpace.Adjoint

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


