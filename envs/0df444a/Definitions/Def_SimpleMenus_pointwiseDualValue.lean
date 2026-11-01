-- Prove2me | Definitions.Def_SimpleMenus_pointwiseDualValue
-- name    : SimpleMenus_pointwiseDualValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:44.262637+00:00
-- url     : https://prove2.me/theorems/ad785670-9ffb-4662-b639-9dabd99e8399
-- title:
--   Dual of the homogenized problem at price $p$
-- statement:
--   For a mechanism $\pi$ and a price $p$, the dual of the homogenized problem is
--
--   $$\sup_{\lambda_0(p)\in\mathbb R,\ \lambda_k(p)\ge0}\lambda_0(p)\quad\text{s.t.}\quad\sum_{k=1}^K\phi_k(w)\lambda_k(p)\le t(w)\ \ (w\in[0,p)),\qquad\lambda_0(p)+\sum_{k=1}^K\phi_k(w)\lambda_k(p)\le t(w)\ \ (w\in[p,\bar v]).$$
--
--   **Formalization Note** The value lies in the extended reals. $\lambda_0$ is free, since its primal constraint is an equality.
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, proof of Proposition 1, p.ec7 (PDF p.41)

import Mathlib
import Definitions.Def_SimpleMenus_pay

open Set

namespace SimpleMenus

/-- The dual of the homogenized nature problem at the price `p`:
`sup λ_0(p)` over `λ_0(p) ∈ ℝ`, `λ_k(p) ≥ 0`, subject to
`Σ_k ϕ_k(w) λ_k(p) ≤ t(w)` for `w ∈ [0, p)` and `λ_0(p) + Σ_k ϕ_k(w) λ_k(p) ≤ t(w)` for
`w ∈ [p, v̄]` (Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, proof of Proposition 1, p.ec7 = PDF p.41).

Formalization Note: the value is in `EReal`; `λ_0` is free (its primal constraint is an equality)
and the `λ_k` are nonnegative. -/
noncomputable def pointwiseDualValue (vbar : ℝ) {K n : ℕ} (phi : Fin K → ℝ → ℝ)
    (v x : Fin n → ℝ) (p : ℝ) : EReal :=
  ⨆ (lam0 : ℝ) (lam : Fin K → ℝ)
    (_ : (∀ k, 0 ≤ lam k) ∧
      (∀ w ∈ Ico 0 p, ∑ k, phi k w * lam k ≤ pay v x w) ∧
      (∀ w ∈ Icc p vbar, lam0 + ∑ k, phi k w * lam k ≤ pay v x w)),
    ((lam0 : ℝ) : EReal)

end SimpleMenus


