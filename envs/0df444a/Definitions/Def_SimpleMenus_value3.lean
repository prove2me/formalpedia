-- Prove2me | Definitions.Def_SimpleMenus_value3
-- name    : SimpleMenus_value3
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:53.928264+00:00
-- url     : https://prove2.me/theorems/627b10cf-3ae3-4773-91b9-28a4ffc3ebf5
-- title:
--   Value of Problem (3) for a fixed mechanism
-- statement:
--   For a fixed $n$-level mechanism $\pi$ (price levels $v$, probabilities $x$), Problem (3) asks for the largest $r\in\mathbb R$ for which there are $\lambda_k(p)\ge0$, $p\in[0,\bar v]$, with
--
--   $$\sum_{k=1}^K\phi_k(w)\lambda_k(p)\le t(w)\quad\forall p\in[0,\bar v],\ \forall w\in[0,p),$$
--   $$r\cdot p+\sum_{k=1}^K\phi_k(w)\lambda_k(p)\le t(w)\quad\forall p\in[0,\bar v],\ \forall w\in[p,\bar v].$$
--
--   The full Problem (3) also optimizes over $\pi\in\Pi_n$; Proposition 1 identifies the value for each $\pi$ with $\mathrm{CR}(\pi)$.
--
--   **Formalization Note** $\lambda$ is any nonnegative function of $p$ (no regularity); only its values on $[0,\bar v]$ enter. The value lies in the extended reals.
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, display (3), p.10

import Mathlib
import Definitions.Def_SimpleMenus_pay

open Set

namespace SimpleMenus

/-- Feasibility in Problem (3) for a fixed mechanism `(v, x)`: `λ(p) ∈ ℝ^K_+` for every
`p ∈ [0, v̄]`, `r ∈ ℝ`, and for every `p ∈ [0, v̄]`:
`Σ_k ϕ_k(w) λ_k(p) ≤ t(w)` for `w ∈ [0, p)` and `r·p + Σ_k ϕ_k(w) λ_k(p) ≤ t(w)` for `w ∈ [p, v̄]`
(Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, display (3), p.10).

Formalization Note: `λ` is any function `ℝ → ℝ^K` (no regularity in `p`), nonnegative
everywhere; only its values on `[0, v̄]` enter the constraints. -/
def Feasible3 (vbar : ℝ) {K n : ℕ} (phi : Fin K → ℝ → ℝ) (v x : Fin n → ℝ) (r : ℝ)
    (lam : ℝ → Fin K → ℝ) : Prop :=
  (∀ p k, 0 ≤ lam p k) ∧
    ∀ p ∈ Icc 0 vbar,
      (∀ w ∈ Ico 0 p, ∑ k, phi k w * lam p k ≤ pay v x w) ∧
      (∀ w ∈ Icc p vbar, r * p + ∑ k, phi k w * lam p k ≤ pay v x w)

/-- The value of Problem (3) for a fixed mechanism `(v, x)`: the supremum of `r` over the
feasible `(r, λ)` (Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, display (3), p.10).

Formalization Note: the value is in `EReal` (`⊤` if unbounded). -/
noncomputable def value3 (vbar : ℝ) {K n : ℕ} (phi : Fin K → ℝ → ℝ) (v x : Fin n → ℝ) :
    EReal :=
  ⨆ (r : ℝ) (lam : ℝ → Fin K → ℝ) (_ : Feasible3 vbar phi v x r lam), ((r : ℝ) : EReal)

end SimpleMenus


