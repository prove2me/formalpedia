-- Prove2me | Definitions.Def_DualRCD_IsProxSupp
-- name    : DualRCD_IsProxSupp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:45:32.031709+00:00
-- url     : https://prove2.me/theorems/01677837-2c61-4b17-83d1-873da91c5e7e
-- title:
--   $p=\mathrm{prox}_{\alpha\cdot\mathrm{supp}_X}(u)$
-- statement:
--   For $\alpha>0$, the point $p$ is the proximal point of $\alpha\cdot\operatorname{supp}_X$ at $u$ if it minimizes
--   $$
--   z\mapsto\frac12\|z-u\|^2+\alpha\cdot\operatorname{supp}_X(z)
--   $$
--   over $\mathbb R^n$. This is the operation performed on the selected block in each RCD iteration, with $\alpha=1$.
--
--   **Formalization Note.** It is an argmin predicate with values in the extended reals.
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, display (18), p.14

import Mathlib
import Definitions.Def_DualRCD_suppFn

namespace DualRCD

/-- `p = prox_{α·supp_X}(u)`, i.e. `p` minimizes `z ↦ ½‖z − u‖² + α·supp_X(z)` over `ℝⁿ` (Necoara &
Fercoq, arXiv:1911.06014v1, display (18), p.14).

**Formalization Note.** An argmin predicate with values in `EReal`, since `supp_X` can be `+∞`.
For `X` nonempty closed convex and `α > 0` the minimizer exists and is unique
(`DualRCD.eq_18_prox_support`). -/
def IsProxSupp {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (α : ℝ)
    (u p : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ z, ((1 / 2 * ‖p - u‖ ^ 2 : ℝ) : EReal) + (α : EReal) * suppFn X p ≤
    ((1 / 2 * ‖z - u‖ ^ 2 : ℝ) : EReal) + (α : EReal) * suppFn X z

end DualRCD


