-- Prove2me | Definitions.Def_SimpleMenus_valueEC8
-- name    : SimpleMenus_valueEC8
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:52.435874+00:00
-- url     : https://prove2.me/theorems/34e8c117-f824-4cf3-a415-8ca2199e7c02
-- title:
--   Value of the reduced program of p.ec8 for fixed $x$
-- statement:
--   For fixed price levels, grid and probabilities $x$, the intermediate program of the proof of Theorem 1 asks for the largest $r\ge0$ for which there are $\lambda_k(p)\ge0$, $p\in[0,\bar v]$, with
--
--   $$\sum_{k=1}^K\underline\phi_{k,j}\lambda_k(p)\le\sum_{l\in S_j}x_lv_l\quad\forall p\in[0,\bar v],\ j=1,\dots,j^\dagger(p),$$
--   $$r\cdot p+\sum_{k=1}^K\underline\phi_{k,j}\lambda_k(p)\le\sum_{l\in S_j}x_lv_l\quad\forall p\in[0,\bar v],\ j=j^\dagger(p)+1,\dots,n+m+1,$$
--
--   where $j^\dagger(p)=\max\{j:u_j\le p\}$.
--
--   **Formalization Note** On a monotone grid, "$j\le j^\dagger(p)$" is "$u_j\le p$". The value lies in the extended reals.
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, proof of Theorem 1, p.ec8 (PDF p.42), display after "obtain an equivalent formulation as follows"

import Mathlib
import Definitions.Def_SimpleMenus_phiLow
import Definitions.Def_SimpleMenus_Rsum

namespace SimpleMenus

/-- Feasibility in the intermediate program of the proof of Theorem 1 (Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, p.ec8 = PDF p.42,
the display after "obtain an equivalent formulation as follows"), for fixed `x`: `r ≥ 0`,
`λ(p) ∈ ℝ^K_+`, and for every `p ∈ [0, v̄]` and grid index `j`:
`Σ_k ϕ̲_{k,j} λ_k(p) ≤ Σ_{l ∈ S_j} x_l v_l` when `u_j ≤ p` (`j ≤ j†(p)`), and
`r·p + Σ_k ϕ̲_{k,j} λ_k(p) ≤ Σ_{l ∈ S_j} x_l v_l` when `p < u_j` (`j > j†(p)`).

Formalization Note: `g` is the extended grid `u_1, …, u_{n+m+1}`, 0-based; `j†(p) = max{j | u_j ≤ p}`,
so for a monotone grid "`j ≤ j†(p)`" is "`u_j ≤ p`". -/
def FeasibleEC8 (vbar : ℝ) {K n M : ℕ} (phi : Fin K → ℝ → ℝ) (v x : Fin n → ℝ)
    (g : Fin M → ℝ) (r : ℝ) (lam : ℝ → Fin K → ℝ) : Prop :=
  0 ≤ r ∧ (∀ p k, 0 ≤ lam p k) ∧
    ∀ p ∈ Set.Icc 0 vbar, ∀ j,
      (g j ≤ p → ∑ k, phiLow phi g k j * lam p k ≤ Rsum v x g j) ∧
      (p < g j → r * p + ∑ k, phiLow phi g k j * lam p k ≤ Rsum v x g j)

/-- The value (supremum of `r`) of the intermediate program of p.ec8 for fixed `x`, in `EReal`. -/
noncomputable def valueEC8 (vbar : ℝ) {K n M : ℕ} (phi : Fin K → ℝ → ℝ) (v x : Fin n → ℝ)
    (g : Fin M → ℝ) : EReal :=
  ⨆ (r : ℝ) (lam : ℝ → Fin K → ℝ) (_ : FeasibleEC8 vbar phi v x g r lam), ((r : ℝ) : EReal)

end SimpleMenus


