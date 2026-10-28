-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_AffineMaximum
-- name    : KLSModular_FunctionalInequalities_Analysis_Convex_AffineMaximum
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:49:45.125571+00:00
-- url     : https://prove2.me/theorems/6ce50813-8eec-46a5-abb0-e806e1385307
-- title:
--   Finite affine maximum
-- statement:
--   For a nonempty finite set $s\subset E$, a real function $a:E\to\mathbb{R}$, and $y\in E$, `affineMaximum s hs a y` is the genuine finite maximum of $\langle x,y\rangle-a(x)$ over $x\in s$. The bundle also contains geometric auxiliary results controlling these maxima and comparing them with the extended-real Legendre transform.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Convex.Legendre
--   import Mathlib.Analysis.Normed.Affine.Convex
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def affineMaximum (s : Finset E) (hs : s.Nonempty) (a : E → ℝ) (y : E) : ℝ :=
--     s.sup' hs (fun x => inner ℝ x y - a x)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Theorems in source order:
--
--   - [`affineMaximum_coercive`](https://prove2.me/theorems/e32066d6-367b-466d-9089-f5d72ac05f70)
--   - [`eventually_affineMaximum_sub_le_legendre`](https://prove2.me/theorems/5b6258b4-53ab-4ec0-9b82-126b22c2ab6c)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/AffineMaximum.lean) · `FunctionalInequalities.Analysis.Convex.AffineMaximum` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/AffineMaximum.lean#L27-L29 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.AffineMaximum`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Convex_AffineMaximum`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Normed.Affine.Convex

noncomputable section
open Filter Set
open scoped Topology
namespace FunctionalInequalities
namespace Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- A genuine finite maximum of the affine summands of a conjugate. -/
def affineMaximum (s : Finset E) (hs : s.Nonempty) (a : E → ℝ) (y : E) : ℝ :=
  s.sup' hs (fun x => inner ℝ x y - a x)
end Analysis
end FunctionalInequalities


