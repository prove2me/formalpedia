-- Prove2me | Definitions.Def_DualRCD_dualFn
-- name    : DualRCD_dualFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:46:22.583061+00:00
-- url     : https://prove2.me/theorems/8f2162ec-1b98-4a1f-a960-4d51b44188f4
-- title:
--   Dual objective $d(y)$, display (10)
-- statement:
--   The dual objective is
--   $$
--   d(y)=g^*\Big(-\sum_{i=1}^my_i\Big)+\sum_{i=1}^m\operatorname{supp}_{X_i}(y_i)=\tilde d(y)+\operatorname{supp}(y).
--   $$
--   It is the sum of a smooth convex function and a separable nonsmooth convex function, the structure that block coordinate descent exploits.
--
--   **Formalization Note.** The value is in the extended reals, and it is $+\infty$ off the domain of the support functions.
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, display (10), p.7

import Mathlib
import Definitions.Def_DualRCD_dTilde
import Definitions.Def_DualRCD_suppFn

namespace DualRCD

/-- The dual objective `d(y) = g*(−Σᵢ yᵢ) + Σᵢ supp_{Xᵢ}(yᵢ)` (Necoara & Fercoq,
arXiv:1911.06014v1, display (10), p.7).

**Formalization Note.** `EReal`-valued: `+∞` off the domain of the support functions. For a strongly
convex `g` the first summand is finite, and for nonempty `Xᵢ` no summand is `⊥`, so EReal's
`⊥ + ⊤ = ⊥` never occurs under the hypotheses of the theorems. -/
noncomputable def dualFn {n m : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (X : Fin m → Set (EuclideanSpace ℝ (Fin n))) (y : DualSpace n m) : EReal :=
  dTilde g y + ∑ i, suppFn (X i) (y i)

end DualRCD


