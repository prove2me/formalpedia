-- Prove2me | Definitions.Def_CondBasedProd_IsHJBSolution
-- name    : CondBasedProd_IsHJBSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:30:32.83856+00:00
-- url     : https://prove2.me/theorems/fb8458cc-8669-40b4-934b-6f64004d8ca7
-- title:
--   The HJB system (2), with the derivative $r(0)$ at the failed level
-- statement:
--   A function $J$ solves the **HJB system** at base rate $\lambda$ if, for $x\le\xi$ and $t\ge0$,
--   $$
--   \partial_tJ(x,t)=\max_{s\in\mathcal S}\bigl[r(s)-\lambda f(s)\bigl(J(x,t)-J(x+1,t)\bigr)\bigr]\quad(x<\xi),\qquad \partial_tJ(\xi,t)=r(0),
--   $$
--   with boundary values $J(x,0)=-c_m(x)$.
--
--   This is display (2) of the source with its second branch corrected. The source prints $0$ there, but its definition (1) has the failed system run at $s=0$ and earn $r(0)$, so the two agree exactly when $r(0)=0$.
--
--   **Formalization Note** The derivative is taken within $[0,\infty)$: one-sided at $t=0$, two-sided for $t>0$.
-- source:
--   Drent, Drent & Arts, Condition-Based Production for Stochastically Deteriorating Systems, arXiv:2308.07507v2, Lemma 1, display (2), p.10; App. A.1, displays (6)–(7), p.34

import Mathlib
import Definitions.Def_CondBasedProd_Model

open Set

namespace CondBasedProd

/-- **The HJB system** (2) of Lemma 1 (arXiv:2308.07507v2, p.10), as corrected: `J : ℕ → ℝ → ℝ`
satisfies, on `x ≤ ξ`, `t ≥ 0`,
`∂_t J(x,t) = max_{s ∈ 𝒮} [r(s) − λ f(s) (J(x,t) − J(x+1,t))]` for `x < ξ`,
`∂_t J(ξ,t) = r(0)`, and `J(x,0) = −c_m(x)`.

**Formalization Note.** The derivative is taken within `[0,∞)`, one-sided at `t = 0` and two-sided
for `t > 0`. The printed second branch is `0`; under the definition (1) the failed system runs at
`s = 0` and keeps earning `r(0)`, so the derivative is `r(0)` (the two agree when `r(0) = 0`). The
maximum is asserted to exist through `IsGreatest`. -/
def IsHJBSolution (M : Model) (lam : ℝ) (J : ℕ → ℝ → ℝ) : Prop :=
  (∀ x ≤ M.ξ, J x 0 = -M.cm x) ∧
  (∀ x < M.ξ, ∀ t, 0 ≤ t → ∃ v,
    IsGreatest ((fun s => M.r s - lam * M.f s * (J x t - J (x + 1) t)) '' Icc 0 M.sbar) v ∧
      HasDerivWithinAt (J x) v (Ici 0) t) ∧
  (∀ t, 0 ≤ t → HasDerivWithinAt (J M.ξ) (M.r 0) (Ici 0) t)

end CondBasedProd


