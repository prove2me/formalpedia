-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Laplacian
-- name    : KLSModular_FunctionalInequalities_Analysis_BakryEmery_Laplacian
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:16:54.75565+00:00
-- url     : https://prove2.me/theorems/6d4fe636-d4d6-41ad-8a90-95a5712d28e4
-- title:
--   Weighted Laplacian and its regularity
-- statement:
--   For functions $U,f:E\to\mathbb R$, `weightedLaplacian U f x` is the diffusion-generator expression $\Delta f(x)-\langle\nabla U(x),\nabla f(x)\rangle$, with the nonnegative semigroup operator corresponding to its negative. If $U$ is $C^1$ and $f$ is $C^2$, `continuous_weightedLaplacian` states that this expression is continuous; if $f$ has compact support, `hasCompactSupport_weightedLaplacian` gives compact support as well. Under a finite Borel measure, `memLp_weightedLaplacian` states membership in $L^p$ for every $p\in[0,\infty]$ represented by `ENNReal`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.BakryEmery.Calculus
--   import Mathlib.MeasureTheory.Function.LpSpace.Indicator
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def weightedLaplacian (U f : E → ℝ) (x : E) : ℝ :=
--     Laplacian.laplacian f x - ⟪gradient U x, gradient f x⟫
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/BakryEmery/Calculus`](https://prove2.me/theorems/aff8478c-96df-49c0-bd72-24bb70d5d99a).
--
--   Theorems in source order:
--
--   - [`weightedLaplacian_eq_zero_of_notMem_tsupport`](https://prove2.me/theorems/b381f334-820c-4611-a1c1-f11888c8bc19)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Laplacian.lean) · `FunctionalInequalities.Analysis.BakryEmery.Laplacian` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Laplacian.lean#L23-L85 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Laplacian`, definition bundle `KLSModular_FunctionalInequalities_Analysis_BakryEmery_Laplacian`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
namespace BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
/-- The weighted Laplacian `ℒ f = Δ f - ⟪∇U, ∇f⟫` of the potential `U`, as a pointwise
differential expression on classical functions. It is the diffusion-generator convention: the
nonnegative operator of the heat semigroup is `-ℒ`. -/
def weightedLaplacian (U f : E → ℝ) (x : E) : ℝ :=
  Laplacian.laplacian f x - ⟪gradient U x, gradient f x⟫
theorem weightedLaplacian_apply (U f : E → ℝ) (x : E) :
    weightedLaplacian U f x = Laplacian.laplacian f x - ⟪gradient U x, gradient f x⟫ := rfl
/-- The weighted Laplacian of a `C²` function for a `C¹` potential is continuous. -/
theorem continuous_weightedLaplacian {U f : E → ℝ} (hU : ContDiff ℝ 1 U) (hf : ContDiff ℝ 2 f) :
    Continuous (weightedLaplacian U f) :=
  (continuous_laplacian hf).sub
    ((continuous_gradient hU).inner (continuous_gradient (hf.of_le (by norm_num))))
/-- The weighted Laplacian of a compactly supported function has compact support. -/
theorem hasCompactSupport_weightedLaplacian (U : E → ℝ) {f : E → ℝ}
    (hfc : HasCompactSupport f) : HasCompactSupport (weightedLaplacian U f) := by
  refine (hasCompactSupport_laplacian hfc).sub ?_
  refine (hasCompactSupport_gradient hfc).mono fun x hx => ?_
  intro h0
  apply hx
  simp [h0]
section Integrable
variable [MeasurableSpace E] [BorelSpace E]
/-- The weighted Laplacian of a `C²` compactly supported function lies in every `L^p` of a finite
measure; the potential need only be `C¹`. -/
theorem memLp_weightedLaplacian {μ : Measure E} [IsFiniteMeasure μ] {U f : E → ℝ}
    (hU : ContDiff ℝ 1 U) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (p : ENNReal) :
    MemLp (weightedLaplacian U f) p μ :=
  (continuous_weightedLaplacian hU hf).memLp_of_hasCompactSupport
    (hasCompactSupport_weightedLaplacian U hfc)
end Integrable
end BakryEmery
end Analysis
end FunctionalInequalities


