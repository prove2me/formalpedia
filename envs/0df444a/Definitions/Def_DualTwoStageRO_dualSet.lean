-- Prove2me | Definitions.Def_DualTwoStageRO_dualSet
-- name    : DualTwoStageRO_dualSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:41.081176+00:00
-- url     : https://prove2.me/theorems/1a7d6c43-7294-4554-a400-8820c48528ea
-- title:
--   The uncertainty set $\mathcal V$ of the dualized model (6)
-- statement:
--   A **dual point** is a quadruple $(u,v,w,z)$ with $u=(u_0,\dots,u_{m_1})$, $u_i\in\mathbb R^{n_y}$, $v,z\in\mathbb R^{m_1+1}$ and $w\in\mathbb R^{m_2}$. The set $\mathcal V$ consists of the dual points with
--
--   1. $v\ge0$ and $v_0=1$;
--   2. $v_i\,(g_i)^*(u_i/v_i)\le z_i$ for $i=0,\dots,m_1$;
--   3. $\sum_{i=0}^{m_1}u_i=-B^\top w$.
--
--   $$\mathcal V=\Bigl\{(u,v,w,z):\ v\ge0,\ v_0=1,\ v_i(g_i)^*\Bigl(\frac{u_i}{v_i}\Bigr)\le z_i,\ i=0,\dots,m_1,\ \sum_{i=0}^{m_1}u_i=-B^\top w\Bigr\}.$$
--
--   In the dualized model the convexity of the recourse functions has moved into this uncertainty set.
--
--   **Formalization Note** $v_i(g_i)^*(u_i/v_i)$ is the closed perspective `perspConj` ($0$ at $v_i=0,u_i=0$, $+\infty$ at $v_i=0,u_i\ne0$). The set is exactly the printed one; it is not restricted to points at which (6)'s inner problem is feasible. The module also defines the structure `DualPoint`.
-- source:
--   de Ruiter, Zhen, den Hertog, Technical Note—Dual Approach for Two-Stage Robust Nonlinear Optimization, Operations Research 71(5):1794–1799, 2023, doi:10.1287/opre.2022.2289 (published version, sha256 75cbce38…fe03ac), Theorem 1, p.1796 (the set V)

import Mathlib
import Definitions.Def_DualTwoStageRO_Problem
import Definitions.Def_DualTwoStageRO_perspConj

namespace DualTwoStageRO

open Matrix

/-- A point `(u, v, w, z)` of the uncertainty set `V` of the dualized model (6):
`u = (u_0,…,u_{m1})` with `u_i ∈ ℝ^{ny}`, `v, z ∈ ℝ^{m1+1}`, `w ∈ ℝ^{m2}`. -/
structure DualPoint (ny m1 m2 : ℕ) where
  /-- `u_i ∈ ℝ^{ny}`, `i = 0,…,m1`. -/
  u : Fin (m1 + 1) → Fin ny → ℝ
  /-- `v ∈ ℝ^{m1+1}`. -/
  v : Fin (m1 + 1) → ℝ
  /-- `w ∈ ℝ^{m2}`. -/
  w : Fin m2 → ℝ
  /-- `z ∈ ℝ^{m1+1}`. -/
  z : Fin (m1 + 1) → ℝ

variable {nx ny nζ m1 m2 p : ℕ}

/-- **The uncertainty set `V` of the dualized model (6).**
de Ruiter, Zhen, den Hertog, *Technical Note—Dual Approach for Two-Stage Robust Nonlinear
Optimization*, Operations Research 71(5), 2023, Theorem 1, p.1796:
`V = {(u,v,w,z) : v ≥ 0, v_0 = 1, v_i (g_i)^*(u_i/v_i) ≤ z_i, i = 0,…,m1, Σ_{i=0}^{m1} u_i = −B⊤w}`.

**Formalization Note.** `v_i (g_i)^*(u_i/v_i)` is `perspConj (P.g i) (u i) (v i)` (closed
perspective: at `v_i = 0` it is `0` for `u_i = 0` and `+∞` otherwise). The set is exactly the printed
one; it is not restricted to points for which (6)'s inner problem is feasible. -/
def dualSet (P : Problem nx ny nζ m1 m2 p) : Set (DualPoint ny m1 m2) :=
  {q | 0 ≤ q.v ∧ q.v 0 = 1 ∧ (∀ i, perspConj (P.g i) (q.u i) (q.v i) ≤ (q.z i : EReal)) ∧
    ∑ i, q.u i = -(P.Bᵀ *ᵥ q.w)}

end DualTwoStageRO


