-- Prove2me | Definitions.Def_SimpleMenus_value4
-- name    : SimpleMenus_value4
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:55.703026+00:00
-- url     : https://prove2.me/theorems/da9bce0e-1aeb-484e-9d1c-af404f94ec1d
-- title:
--   Value of the finite linear program (4)
-- statement:
--   For fixed price levels and grid, Problem (4) is
--
--   $$\sup_{\lambda\in\mathbb R_+^{K\times(m+n+1)},\ x\in\mathbb R^n_+,\ r\in\mathbb R_+} r$$
--
--   subject to, for every $i\in[n+m+1]$,
--
--   $$\sum_{k=1}^K\underline\phi_{k,j}\lambda_{k,i}\le\sum_{l\in S_j}v_lx_l\quad(j\in[i-1]),\qquad r\cdot u_i+\sum_{k=1}^K\underline\phi_{k,j}\lambda_{k,i}\le\sum_{l\in S_j}v_lx_l\quad(j=i,\dots,n+m+1),$$
--
--   and $\sum_{i=1}^n x_i=1$. The item defines the value for a fixed $x$ (the supremum over $r$ and $\lambda$) and the optimal value of the whole program (the supremum over $x$ in the probability simplex as well).
--
--   **Formalization Note** Indices are 0-based: "$j\in[i-1]$" is $j<i$ and "$j=i,\dots,n+m+1$" is $i\le j$; the second family carries $r\cdot u_i$, the column's own grid point. Values lie in the extended reals ($+\infty$ if unbounded).
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, display (4), p.11

import Mathlib
import Definitions.Def_SimpleMenus_phiLow
import Definitions.Def_SimpleMenus_Rsum

namespace SimpleMenus

/-- Feasibility in the finite linear program (4) for fixed `x` (Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, display (4), p.11):
`r ≥ 0`, `λ ∈ ℝ^{K×(n+m+1)}_+`, and for every `i`:
`Σ_k ϕ̲_{k,j} λ_{k,i} ≤ Σ_{l ∈ S_j} v_l x_l` for `j ∈ [i − 1]`, and
`r·u_i + Σ_k ϕ̲_{k,j} λ_{k,i} ≤ Σ_{l ∈ S_j} v_l x_l` for `j = i, …, n + m + 1`.

Formalization Note: 0-based indices on the extended grid `g = (u_1, …, u_{n+m+1})`: "`j ∈ [i−1]`"
is `j < i` and "`j = i, …, n+m+1`" is `i ≤ j`. The second family carries `r·u_i` (the column's
index), as printed. -/
def Feasible4 {K n M : ℕ} (phi : Fin K → ℝ → ℝ) (v x : Fin n → ℝ) (g : Fin M → ℝ) (r : ℝ)
    (lam : Fin K → Fin M → ℝ) : Prop :=
  0 ≤ r ∧ (∀ k i, 0 ≤ lam k i) ∧
    ∀ i j,
      (j < i → ∑ k, phiLow phi g k j * lam k i ≤ Rsum v x g j) ∧
      (i ≤ j → r * g i + ∑ k, phiLow phi g k j * lam k i ≤ Rsum v x g j)

/-- The value of (4) for fixed `x`: the supremum of `r` over the feasible `(r, λ)`, in `EReal`
(`⊤` if unbounded). -/
noncomputable def value4 {K n M : ℕ} (phi : Fin K → ℝ → ℝ) (v x : Fin n → ℝ) (g : Fin M → ℝ) :
    EReal :=
  ⨆ (r : ℝ) (lam : Fin K → Fin M → ℝ) (_ : Feasible4 phi v x g r lam), ((r : ℝ) : EReal)

/-- The optimal value of the finite linear program (4): the supremum over `x ∈ ℝ^n_+` with
`Σ_i x_i = 1` (the standard simplex) and over `(r, λ)` (Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, display (4), p.11). -/
noncomputable def value4Joint {K n M : ℕ} (phi : Fin K → ℝ → ℝ) (v : Fin n → ℝ)
    (g : Fin M → ℝ) : EReal :=
  ⨆ x ∈ stdSimplex ℝ (Fin n), value4 phi v x g

end SimpleMenus


