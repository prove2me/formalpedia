-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
-- name    : KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:36:10.42273+00:00
-- url     : https://prove2.me/theorems/f75aebf0-5b0f-44ee-8e77-f15b658490b5
-- title:
--   Weak directional derivative
-- statement:
--   `HasWeakDerivAlong f g v` means that $f$ and $g$ are locally integrable with respect to Lebesgue measure and that, for every $C^1$ compactly supported test function $\psi$, $\int f(x)\,Df(x)[v]$ is replaced by the distributional identity $\int f(x)D\psi(x)[v]$ $=-\int g(x)\psi(x)\,dx$. Thus `g` is the weak directional derivative of `f` along $v$, with all integrability and test-function conditions explicit.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Basic.lean#L20-L26 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Basic`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.SpecificCodomains.Pi

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


