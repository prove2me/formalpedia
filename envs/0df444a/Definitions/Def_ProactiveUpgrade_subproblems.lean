-- Prove2me | Definitions.Def_ProactiveUpgrade_subproblems
-- name    : ProactiveUpgrade_subproblems
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:51:31.087413+00:00
-- url     : https://prove2.me/theorems/1a9c5d8b-3ef2-4200-9e1b-d211f1d0a589
-- title:
--   The subproblems $\hat v_{1,t}$, $\hat v_{2,t}$ of Lemma 3
-- statement:
--   When product $i$ is out of stock ($x_i=0$), no customer is ever served from product $i$ again, and products $\{1,\dots,i-1\}$ and $\{i,\dots,m\}$ never interact. The two subproblems are the same model on fewer products:
--
--   1. **low subproblem**: products $1,\dots,i-1$ with the same prices, request and acceptance probabilities; requests for products $i,\dots,m$ count as no-requests, $\beta_0^{L}=\beta_0+\sum_{k\ge i}\beta_k$. Its top product $i-1$ has no upgrade, since product $i$ is out of stock. Its optimal profit function is $\hat v_{1,t}(x_1,\dots,x_{i-1})$.
--   2. **high subproblem**: products $i,\dots,m$ with the same data; requests for products $1,\dots,i-1$ count as no-requests, $\beta_0^{H}=\beta_0+\sum_{k<i}\beta_k$. Product $i$ has zero stock but its customers may still be upgraded to $i+1$. Its optimal profit function, as a function of $(x_{i+1},\dots,x_m)$ with $x_i=0$, is $\hat v_{2,t}(x_{i+1},\dots,x_m)$.
--
--   **Formalization Note** For $i=1$ the low subproblem has no products and value $0$; for $i=m$ the high subproblem has only product $m$ at zero stock and value $0$.
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, Lemma 3, p.24; Proof of Lemma 3, pp.36–37; Proposition 4, p.24

import Mathlib
import Definitions.Def_ProactiveUpgrade_vhat

namespace ProactiveUpgrade

/-- The subproblem of products `{1, …, i − 1}` (Lemma 3, p.24; Proof of Lemma 3, pp.36–37) when
product `i` (0-based index `i`) is out of stock: the same prices, request and acceptance
probabilities on `Fin i`, and requests for products `i, …, m` become no-requests,
`β₀ᴸ = β₀ + Σ_{k ≥ i} β_k`. Its top product has no upgrade (its successor is out of stock). -/
def lowModel {m : ℕ} (M : Model m) (i : Fin m) : Model i.val where
  p k := M.p (Fin.castLE i.isLt.le k)
  β k := M.β (Fin.castLE i.isLt.le k)
  β0 := M.β0 + ∑ k ∈ Finset.univ.filter (fun k : Fin m => i ≤ k), M.β k
  q k := M.q (Fin.castLE i.isLt.le k)
  lam := M.lam

/-- The subproblem of products `{i, …, m}` (Lemma 3, p.24) when product `i` is out of stock: the
same data on `Fin (m − i)` (0-based: products `i, …, m − 1`), and requests for products
`1, …, i − 1` become no-requests, `β₀ᴴ = β₀ + Σ_{k < i} β_k`. -/
def highModel {m : ℕ} (M : Model m) (i : Fin m) : Model (m - i.val) where
  p k := M.p ⟨i.val + k.val, by omega⟩
  β k := M.β ⟨i.val + k.val, by omega⟩
  β0 := M.β0 + ∑ k ∈ Finset.univ.filter (fun k : Fin m => k < i), M.β k
  q k := M.q ⟨i.val + k.val, by omega⟩
  lam := M.lam

/-- **`v̂_{1,t}(x₁, …, x_{i−1})`** of Lemma 3 and Proposition 4 (p.24): the optimal profit function
of the subproblem of products `{1, …, i − 1}`. -/
def lowValue {m : ℕ} (M : Model m) (T : ℕ) (i : Fin m) (t : ℕ) (y : Fin i.val → ℕ) : ℝ :=
  vhat (lowModel M i) T t y

/-- **`v̂_{2,t}(x_{i+1}, …, x_m)`** of Lemma 3 and Proposition 4 (p.24): the optimal profit function
of the subproblem of products `{i, …, m}` with `xᵢ = 0`, as a function of the inventories of
products `i + 1, …, m`. -/
def highValue {m : ℕ} (M : Model m) (T : ℕ) (i : Fin m) (t : ℕ)
    (y : Fin (m - (i.val + 1)) → ℕ) : ℝ :=
  vhat (highModel M i) T t (fun k => if h : k.val = 0 then 0 else y ⟨k.val - 1, by omega⟩)

end ProactiveUpgrade


