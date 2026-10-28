-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Gamma
-- name    : KLSModular_FunctionalInequalities_Analysis_BakryEmery_Gamma
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:17:26.089324+00:00
-- url     : https://prove2.me/theorems/6b6aef00-0f84-4633-a830-e04239f02b6b
-- title:
--   Carré du champ definitions
-- statement:
--   For functions on a complete real inner-product space, `gamma f g x` is the pointwise carré du champ $\Gamma(f,g)(x)=\langle\nabla f(x),\nabla g(x)\rangle$. In finite dimension, `gammaTwo U f x` is the iterated carré du champ in the diffusion convention $\Gamma_2(f)=\frac12\mathcal L(\Gamma(f,f))-\Gamma(f,\mathcal Lf)$, where $\mathcal L$ is `weightedLaplacian` and the final pairing is interpreted geometrically through `gamma`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.BakryEmery.Laplacian
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def gamma (f g : E → ℝ) (x : E) : ℝ := ⟪gradient f x, gradient g x⟫
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/BakryEmery/Laplacian`](https://prove2.me/theorems/6d4fe636-d4d6-41ad-8a90-95a5712d28e4).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Gamma.lean) · `FunctionalInequalities.Analysis.BakryEmery.Gamma` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Gamma.lean#L27-L95 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Gamma`, definition bundle `KLSModular_FunctionalInequalities_Analysis_BakryEmery_Gamma`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Laplacian

noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
namespace BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gamma
variable [CompleteSpace E]
/-- The **carré du champ** `Γ(f, g)(x) = ⟪∇f(x), ∇g(x)⟫`, defined geometrically. -/
def gamma (f g : E → ℝ) (x : E) : ℝ := ⟪gradient f x, gradient g x⟫
variable [FiniteDimensional ℝ E]
/-- The **iterated carré du champ** in the diffusion convention,
`Γ₂(f) = ℒ(Γ(f, f)) / 2 - Γ(f, ℒf)`, with `Γ(f, ℒf) = ⟪∇f, ∇(ℒf)⟫` read geometrically. -/
def gammaTwo (U f : E → ℝ) (x : E) : ℝ :=
  weightedLaplacian U (fun y => gamma f f y) x / 2 - gamma f (weightedLaplacian U f) x
end Gamma
end BakryEmery
end Analysis
end FunctionalInequalities


