-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Energy_CovarianceGradient_Translation
-- name    : KLSModular_FunctionalInequalities_Energy_CovarianceGradient_Translation
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:24:25.471794+00:00
-- url     : https://prove2.me/theorems/707a03ec-125b-44b1-be52-91f91946c0fb
-- title:
--   Translation of covariance-gradient tests
-- statement:
--   `Euclidean.gradient_comp_const_add` identifies the gradient of $y\mapsto g(c+y)$ with the translated gradient, and `lipschitzWith_const_add` records that translation is 1-Lipschitz. `CovarianceGradient.Test.translate` composes a covariance-gradient test for ν₂ with $x\mapsto c+x$ to obtain a test for ν₁, assuming the translation is measure-preserving and the covariance operators are equal. The resulting statement includes the required Lipschitz, $L^2$, and integrability fields but does not itself assert equality of relaxation constants.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.L2.Transport
--   import FunctionalInequalities.Energy.CovarianceGradient.Basic
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   def translate
--       (hmp : MeasurePreserving (fun x ↦ c + x) (ν₁ : Measure V) (ν₂ : Measure V))
--       (hcov : Covariance.operator (ν₂ : Measure V) = Covariance.operator (ν₁ : Measure V))
--       (g : Test ν₂) : Test ν₁
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`L2/Transport`](https://prove2.me/theorems/18833b5b-77e3-4a08-986b-55e8c2b513b7), [`Energy/CovarianceGradient/Basic`](https://prove2.me/theorems/517395bc-0a9a-4b82-b89c-ca3b5281db43).
--
--   Theorems in source order:
--
--   - [`relaxation_translateLaw`](https://prove2.me/theorems/b4c355ab-cc76-40d6-94c9-673aabcb6e41)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/CovarianceGradient/Translation.lean) · `FunctionalInequalities.Energy.CovarianceGradient.Translation` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/CovarianceGradient/Translation.lean#L40-L82 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.CovarianceGradient.Translation`, definition bundle `KLSModular_FunctionalInequalities_Energy_CovarianceGradient_Translation`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_L2_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_CovarianceGradient_Basic

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


