-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Affine
-- name    : KLSModular_FunctionalInequalities_Analysis_Convex_Affine
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:57:21.889157+00:00
-- url     : https://prove2.me/theorems/ba0d4420-d959-4afc-bf5b-05caa7b55a1c
-- title:
--   Affine subtraction from an extended-real potential
-- statement:
--   For $f:E\to\overline{\mathbb{R}}$, $a\in E$, $b\in\mathbb{R}$, and $x\in E$, `affineSubtract f a b x` is $f(x)-(\langle a,x\rangle+b)$, with the affine function coerced into the extended reals. The module records pointwise transformation properties of Legendre transforms, epigraph convexity, and normalization under such affine shifts.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Convex.Legendre
--   import FunctionalInequalities.Analysis.Convex.SupportingPlane
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def affineSubtract (f : E → EReal) (a : E) (b : ℝ) (x : E) : EReal :=
--     f x - ((inner ℝ a x + b : ℝ) : EReal)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81), [`Analysis/Convex/SupportingPlane`](https://prove2.me/theorems/49dea8f8-70b2-49f6-b236-fded64ed171f).
--
--   Theorems in source order:
--
--   - [`legendre_affineSubtract`](https://prove2.me/theorems/86cc89dc-153b-4ec4-a574-1e72902d9a9b)
--   - [`convex_epigraph_affineSubtract`](https://prove2.me/theorems/ddb03546-bc6f-456e-b9a9-168872a634c9)
--   - [`exists_nonnegative_origin_zero_affine`](https://prove2.me/theorems/23dc8e13-df9f-4967-b282-729c3b46dcf2)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Affine.lean) · `FunctionalInequalities.Analysis.Convex.Affine` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Affine.lean#L24-L26 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Affine`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Convex_Affine`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SupportingPlane

noncomputable section
namespace FunctionalInequalities
namespace Analysis
section
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Subtract the actual affine function `inner a x + b`. -/
def affineSubtract (f : E → EReal) (a : E) (b : ℝ) (x : E) : EReal :=
  f x - ((inner ℝ a x + b : ℝ) : EReal)
end
end Analysis
end FunctionalInequalities


