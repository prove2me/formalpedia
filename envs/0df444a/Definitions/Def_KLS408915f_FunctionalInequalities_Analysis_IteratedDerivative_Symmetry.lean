-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
-- name    : KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T11:43:00.637858+00:00
-- url     : https://prove2.me/theorems/d0570f1d-8e8a-4189-9d3b-fd10d2ab34fe
-- title:
--   Directional derivatives along an ordered list
-- statement:
--   `directional hs f` recursively applies Fréchet derivatives of a map $f:E\to F$ in the inherited order of the list `hs`: the empty list returns $f$, while prepending $h$ differentiates the result for the tail in direction $h$. The definition assumes only real normed-space structures on $E$ and $F$; the module documentation records related symmetry results, but this bundle provides the definition itself.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/IteratedDerivative/Symmetry.lean#L24-L27 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.IteratedDerivative.Symmetry`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry`; the repository is private at upload time).

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


