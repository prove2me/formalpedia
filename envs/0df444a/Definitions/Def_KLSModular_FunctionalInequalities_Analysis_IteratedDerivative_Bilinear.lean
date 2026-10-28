-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear
-- name    : KLSModular_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:57:58.326988+00:00
-- url     : https://prove2.me/theorems/c2e12327-8e36-4fb7-a6f8-00519f39d229
-- title:
--   Boolean selection of derivative slots
-- statement:
--   `selected h q` takes an ordered family $h:\mathrm{Fin}\,m\to E$ and a Boolean mask $q:\mathrm{Fin}\,m\to\mathrm{Bool}$, retaining precisely the slots for which $q$ is `true`, in their inherited order. The empty family yields the empty list, and the recursion proceeds through `Fin.tail`; this is the slot-allocation object used in raw bilinear Leibniz expansions.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.IteratedDerivative.Symmetry
--   import Mathlib.Analysis.Calculus.FDeriv.Bilinear
--   import Mathlib.Algebra.BigOperators.Group.Finset.Pi
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def selected : {m : ℕ} → (Fin m → E) → (Fin m → Bool) → List E
--     | 0, _, _ => []
--     | _m+1, h, q => if q 0 then h 0 :: selected (Fin.tail h) (Fin.tail q)
--         else selected (Fin.tail h) (Fin.tail q)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/IteratedDerivative/Symmetry`](https://prove2.me/theorems/c3281ab2-65ad-4ae5-995a-70d685aba1dc).
--
--   Theorems in source order:
--
--   - [`directional_bilinear`](https://prove2.me/theorems/c7268247-0081-4a71-b098-d28d94f91226)
--   - [`sum_filter_eq_two_mul_sum_filter_of_compl_invariant`](https://prove2.me/theorems/df0e8f70-61ce-476e-a922-0def8bd9c052)
--   - [`selected_mask_partition`](https://prove2.me/theorems/cf1a6d5b-9b6d-481c-ae20-5dfef1453e3e)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/IteratedDerivative/Bilinear.lean) · `FunctionalInequalities.Analysis.IteratedDerivative.Bilinear` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/IteratedDerivative/Bilinear.lean#L26-L30 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.IteratedDerivative.Bilinear`, definition bundle `KLSModular_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

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


