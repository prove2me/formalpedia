-- Prove2me | Definitions.Def_NetBilinear_Supplement_BilinearSet
-- name    : NetBilinear_Supplement_BilinearSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:41:28.334345+00:00
-- url     : https://prove2.me/theorems/f305b866-b44e-508b-8d72-17455d831f61
-- title:
--   The bilinear set $\mathcal S=\{(x;y;z)\in\Xi\times\Delta_m\times\mathbb R^\kappa : y^\top A^kx=z_k\}$ over a polytope $\Xi=\{Ex\ge f,\ 0\le x\le u\}$
-- statement:
--   Let $N=\{1,\dots,n\}$, $M=\{1,\dots,m\}$, $K=\{1,\dots,\kappa\}$ and $T=\{1,\dots,\tau\}$. Given $E\in\mathbb R^{\tau\times n}$, $f\in\mathbb R^\tau$, $u\in\mathbb R^n$ and matrices $A^k\in\mathbb R^{m\times n}$ ($k\in K$), each with all entries zero except one equal to one, consider
--   $$
--   \mathcal S=\{(x;y;z)\in\Xi\times\Delta_m\times\mathbb R^\kappa : y^\top A^kx=z_k,\ \forall k\in K\},
--   $$
--   where $\Xi=\{x\in\mathbb R^n : Ex\ge f,\ 0\le x\le u\}$ and $\Delta_m=\{y\in\mathbb R^m_+ : \mathbf 1^\top y\le 1\}$. If $A^k_{ji}=1$, the bilinear constraint $k$ is $y_jx_i=z_k$.
--
--   The definition provides the data of $\mathcal S$, the predicate "$(x,y,z)$ satisfies the linear constraints of $\Xi$ and $\Delta_m$" ($z$ free), and the set $\mathcal S$ itself.
--
--   **Formalization Note** Each $A^k$ is given by the position $(i,j)$ of its unique entry $1$. The rows $T$ are an arbitrary index type.
-- source:
--   Khademnia & Davarnia, Convexification of Bilinear Terms over Network Polytopes, arXiv:2302.14151v2, §1, p.2 (the set S)

import Mathlib

namespace NetBilinear.Supplement

/-- **The data of the bilinear set `S`** (Khademnia & Davarnia, *Convexification of Bilinear
Terms over Network Polytopes*, arXiv:2302.14151v2, §1, p.2): for `N = {1,…,n}` (variables `x`),
`M = {1,…,m}` (variables `y`), `K = {1,…,κ}` (variables `z`) and `T = {1,…,τ}` (rows),
`S = {(x;y;z) ∈ Ξ × Δ_m × ℝ^κ | yᵀA^k x = z_k, ∀ k ∈ K}` with
`Ξ = {x ∈ ℝⁿ | Ex ≥ f, 0 ≤ x ≤ u}` and `Δ_m = {y ∈ ℝ^m_+ | 1ᵀy ≤ 1}`, where `E ∈ ℝ^{τ×n}`,
`f ∈ ℝ^τ`, `u ∈ ℝⁿ`, and each `A^k ∈ ℝ^{m×n}` has all entries zero except one equal to one:
if `A^k_{ji} = 1` the bilinear constraint `k` is `y_j x_i = z_k`.

**Formalization Note.** `A^k` is given by the position `pos k = (i, j)` of its unique entry
`1`, so the bilinear constraint `k` reads `y_j x_i = z_k`. The rows `T` are an index type `R`. -/
structure BilinearSet (N M K R : Type*) where
  /-- The constraint matrix `E` of `Ex ≥ f` (row `t`, column `i`). -/
  E : R → N → ℝ
  /-- The right-hand side `f`. -/
  f : R → ℝ
  /-- The upper bounds `u`. -/
  u : N → ℝ
  /-- `pos k = (i, j)` when `A^k_{ji} = 1`. -/
  pos : K → N × M

namespace BilinearSet

variable {N M K R : Type*} [Fintype N] [Fintype M]

/-- **The linear constraints of `Ξ` and `Δ_m`** (arXiv:2302.14151v2, p.2): `Ex ≥ f`,
`0 ≤ x ≤ u`, `y ≥ 0`, `1ᵀy ≤ 1`; `z ∈ ℝ^κ` is free. A point is `(x, y, z)`. -/
def InXiDelta (S : BilinearSet N M K R) (p : (N → ℝ) × (M → ℝ) × (K → ℝ)) : Prop :=
  (∀ t, S.f t ≤ ∑ i, S.E t i * p.1 i) ∧ (∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ S.u i) ∧
    (∀ j, 0 ≤ p.2.1 j) ∧ ∑ j, p.2.1 j ≤ 1

/-- **The set `S`** (arXiv:2302.14151v2, p.2): the points of `Ξ × Δ_m × ℝ^κ` with
`y_j x_i = z_k` for every `k` with `A^k_{ji} = 1`. -/
def carrier (S : BilinearSet N M K R) : Set ((N → ℝ) × (M → ℝ) × (K → ℝ)) :=
  {p | S.InXiDelta p ∧ ∀ k, p.2.1 (S.pos k).2 * p.1 (S.pos k).1 = p.2.2 k}

end BilinearSet

end NetBilinear.Supplement


