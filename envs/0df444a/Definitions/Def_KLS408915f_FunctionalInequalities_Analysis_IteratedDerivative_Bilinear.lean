-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear
-- name    : KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T11:44:21.235757+00:00
-- url     : https://prove2.me/theorems/37766302-5cc9-4dfd-9a45-75d6ddc99ac8
-- title:
--   Boolean selection of derivative slots
-- statement:
--   `selected h q` takes an ordered family $h:\mathrm{Fin}\,m\to E$ and a Boolean mask $q:\mathrm{Fin}\,m\to\mathrm{Bool}$, retaining precisely the slots for which $q$ is `true`, in their inherited order. The empty family yields the empty list, and the recursion proceeds through `Fin.tail`; this is the slot-allocation object used in raw bilinear Leibniz expansions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/IteratedDerivative/Bilinear.lean#L26-L30 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.IteratedDerivative.Bilinear`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.List.FinRange

noncomputable section
open scoped ContDiff
namespace FunctionalInequalities
namespace Analysis
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
/-- Select a subset of the original ordered slots using its Boolean indicator. -/
def selected : {m : ℕ} → (Fin m → E) → (Fin m → Bool) → List E
  | 0, _, _ => []
  | _m+1, h, q => if q 0 then h 0 :: selected (Fin.tail h) (Fin.tail q)
      else selected (Fin.tail h) (Fin.tail q)
end Analysis
end FunctionalInequalities


