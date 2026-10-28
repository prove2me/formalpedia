-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
-- name    : KLSModular_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:57:38.178268+00:00
-- url     : https://prove2.me/theorems/c3281ab2-65ad-4ae5-995a-70d685aba1dc
-- title:
--   Directional derivatives along an ordered list
-- statement:
--   `directional hs f` recursively applies Fréchet derivatives of a map $f:E\to F$ in the inherited order of the list `hs`: the empty list returns $f$, while prepending $h$ differentiates the result for the tail in direction $h$. The definition assumes only real normed-space structures on $E$ and $F$; the module documentation records related symmetry results, but this bundle provides the definition itself.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.Calculus.FDeriv.Symmetric
--   import Mathlib.Data.List.FinRange
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def directional : List E → (E → F) → E → F
--     | [], f => f
--     | h :: hs, f => fun x => fderiv ℝ (directional hs f) x h
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/IteratedDerivative/Symmetry.lean) · `FunctionalInequalities.Analysis.IteratedDerivative.Symmetry` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/IteratedDerivative/Symmetry.lean#L24-L27 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.IteratedDerivative.Symmetry`, definition bundle `KLSModular_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry`; the repository is private at upload time).

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.List.FinRange

noncomputable section
open scoped ContDiff
namespace FunctionalInequalities
namespace Analysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- Successive directional derivatives in the inherited list order. -/
def directional : List E → (E → F) → E → F
  | [], f => f
  | h :: hs, f => fun x => fderiv ℝ (directional hs f) x h
end Analysis
end FunctionalInequalities


