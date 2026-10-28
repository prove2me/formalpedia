-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Proximal
-- name    : KLSModular_FunctionalInequalities_Analysis_Convex_Proximal
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:52:42.894947+00:00
-- url     : https://prove2.me/theorems/1d665bc1-5792-4d08-9238-1bf12adef58c
-- title:
--   Proximal point selector
-- statement:
--   For $f:E\to\mathbb{R}$ and $z\in E$, `proximalPoint f z` is the classical choice of a point $x$ satisfying $f(x)+\langle z-x,y-x\rangle\le f(y)$ for every $y\in E$, selected by `Classical.epsilon`. This expresses the resolvent condition $z-x\in\partial f(x)$; existence and uniqueness for convex finite-dimensional functions are discussed by the surrounding development rather than assumed in this definition.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Convex.Subgradient
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def proximalPoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → ℝ) (z : E) : E :=
--     Classical.epsilon fun x => ∀ y, f x + ⟪z - x, y - x⟫ ≤ f y
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Theorems in source order:
--
--   - [`lipschitzWith_proximalPoint`](https://prove2.me/theorems/400fd9e1-fb0c-4e87-8ab5-d48890ee12a0)
--   - [`hasFDerivAt_half_sq_sub_moreau`](https://prove2.me/theorems/746705d4-4726-407e-8f1b-f9fdde75a858)
--   - [`inner_hasFDerivAt_resolvent_symm`](https://prove2.me/theorems/403fd5b6-c99c-485d-b4de-1d3af30e51e9)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Proximal.lean) · `FunctionalInequalities.Analysis.Convex.Proximal` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Proximal.lean#L126-L130 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Proximal`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Convex_Proximal`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
section LT12D2ProximalPoint
open Set
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The **proximal point** (resolvent of the subdifferential) of `f` at `z`: a point `x` such that
`z − x` is a subgradient of `f` at `x`, i.e. the minimiser of `x ↦ f x + ½‖x − z‖²` (weak Letwin route,
Alexandrov's theorem). For convex `f` on a finite-dimensional space it exists and is unique. -/
def proximalPoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → ℝ) (z : E) : E :=
  Classical.epsilon fun x => ∀ y, f x + ⟪z - x, y - x⟫ ≤ f y
end InnerProduct
end Analysis
end FunctionalInequalities
end LT12D2ProximalPoint


