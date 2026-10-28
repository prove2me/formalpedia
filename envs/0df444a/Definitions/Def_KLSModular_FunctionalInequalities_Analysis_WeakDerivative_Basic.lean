-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic
-- name    : KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:17:48.335989+00:00
-- url     : https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11
-- title:
--   Weak directional derivative
-- statement:
--   `HasWeakDerivAlong f g v` means that $f$ and $g$ are locally integrable with respect to Lebesgue measure and that, for every $C^1$ compactly supported test function $\psi$, $\int f(x)\,Df(x)[v]$ is replaced by the distributional identity $\int f(x)D\psi(x)[v]$ $=-\int g(x)\psi(x)\,dx$. Thus `g` is the weak directional derivative of `f` along $v$, with all integrability and test-function conditions explicit.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Mollification.Basic
--   import Mathlib
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def HasWeakDerivAlong (f g : E → ℝ) (v : E) : Prop :=
--     LocallyIntegrable f (volume : Measure E) ∧ LocallyIntegrable g (volume : Measure E) ∧
--       ∀ ψ : E → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
--         ∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E) = -∫ x, g x * ψ x ∂(volume : Measure E)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Mollification/Basic`](https://prove2.me/theorems/b351487c-eaef-4d4f-b656-728d01c5702d).
--
--   Theorems in source order:
--
--   - [`hasWeakDerivAlong_of_contDiff`](https://prove2.me/theorems/4e2a811d-5127-4a66-87f8-6417e73ed552)
--   - [`hasWeakDerivAlong_of_lipschitz`](https://prove2.me/theorems/b9fc0ec0-1bac-4138-9d6d-d21b20f114b9)
--   - [`HasWeakDerivAlong.mul_contDiff`](https://prove2.me/theorems/2a566c7d-243e-41f1-be35-eae8ff92ebb5)
--   - [`HasWeakDerivAlong.congr_ae`](https://prove2.me/theorems/feacd1e3-2d93-4444-8c84-fe52a0849220)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Basic.lean) · `FunctionalInequalities.Analysis.WeakDerivative.Basic` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Basic.lean#L20-L26 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Basic`, definition bundle `KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Basic
import Mathlib

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace FunctionalInequalities
namespace Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- `g` is the **weak directional derivative** of `f` along `v`, tested against `C¹` functions with
compact support; both functions are locally integrable (so the integrals are not junk). Weak Letwin
route (routes/letwin-weak-definitions.md, item 4). -/
def HasWeakDerivAlong (f g : E → ℝ) (v : E) : Prop :=
  LocallyIntegrable f (volume : Measure E) ∧ LocallyIntegrable g (volume : Measure E) ∧
    ∀ ψ : E → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      ∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E) = -∫ x, g x * ψ x ∂(volume : Measure E)
end Analysis
end FunctionalInequalities
universe u


