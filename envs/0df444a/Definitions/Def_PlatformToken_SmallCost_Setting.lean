-- Prove2me | Definitions.Def_PlatformToken_SmallCost_Setting
-- name    : PlatformToken_SmallCost_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:41.601526+00:00
-- url     : https://prove2.me/theorems/d64c67f5-8400-4931-87a9-3795fc7bacc1
-- title:
--   Platform tokenization: iso-elastic demand, supply and capacity cost, the surplus $\mathcal F$ and the entrepreneur's objective
-- statement:
--   This module fixes the primitives of the platform-financing model of Chod, Trichakis and Yang in the iso-elastic specification of their §5.
--
--   **Parameters.** A parameter vector $p=(a,b,m,n,K,k,c,\gamma,\delta,v)$ consists of demand exponents $a,b$, supply parameters $m,n$, capacity-cost parameters $K,k$, the sellers' cost of joining $c$, the unit cost of effort $\gamma$, the discount factor $\delta$ and the token velocity $v$. The **standing assumptions** are
--   1. $0<a<b<1$, $m\ge 0$, $n\ge 0$, $k>(1-b)/(1-a)$ (§5, p. 10), and $v\ge 1$ (p. 9);
--   2. $0<\delta<1$, $c\ge 0$, $\gamma>0$, $K\ge 0$ (used throughout the paper but never stated).
--
--   For a real $K$, $p[K]$ denotes the same vector with the capacity-cost scale replaced by $K$.
--
--   **Primitives.** For effort $e$ and quantity $q$ (or capacity $Q$),
--   $$d(e,q)=e^a q^{-b},\qquad s(q)=m q^n,\qquad C(Q)=KQ^k,$$
--   the surplus (8)
--   $$\mathcal F(e,q)=q\bigl(d(e,q)-s(q)\bigr),$$
--   and the partial derivatives in $e$, in closed form,
--   $$\mathcal F_e(e,Q)=a e^{a-1}Q^{1-b},\qquad d_e(e,Q)=a e^{a-1}Q^{-b}.$$
--   The entrepreneur's objective, common to (17), (33) and (37), is
--   $$\mathcal F(e,Q)/(1-\delta)-cQ-C(Q)-\gamma e .$$
--   The revenue in period $i$ is $\pi(x_i,q_i)=x_i\,d(e,q_i)\,q_i$ (1); at the equilibrium fees (9)–(10) and $\bar q_i=Q$ this gives
--   $$\pi(\bar x_1,\bar q_1)=\bigl(d(e,Q)-s(Q)-c\bigr)Q,\qquad \pi(\bar x_i,\bar q_i)=\bigl(d(e,Q)-s(Q)\bigr)Q\quad(i\ge 2).$$
--
--   These are the common objects of every statement of the mission.
--
--   **Formalization Note** Powers are real powers (`Real.rpow`), for which $0^y=0$ when $y\neq 0$; so $d(e,0)=0$ (the paper's value is $+\infty$) and $\mathcal F_e$, $d_e$ vanish at $e=0$ or $Q=0$. These boundary values only enter at points the programs exclude. That the closed forms are the partial derivatives is stated as the helper theorems `Fe_hasDerivAt` and `de_hasDerivAt`. The parameters $\gamma,\delta$ are the fields `γ`, `δ`; the capacity cost is `Ccap`.
-- source:
--   Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard, Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, pp. 5–6, (1), (8), (9)–(10); pp. 8–9, v ≥ 1; p. 10, §5 (iso-elastic forms)

import Mathlib

set_option autoImplicit false

/-!
# Platform tokenization: the iso-elastic model (Chod, Trichakis, Yang 2022, §2–§5)

Chod, Trichakis, Yang, Platform Tokenization: Financing, Governance, and Moral Hazard,
Management Science (Articles in Advance, 2022), doi:10.1287/mnsc.2021.4225, pp. 4–10:
the primitives of §2 (p. 5), the surplus (8) (p. 6), the fees (9)–(10) with the revenue (1)
(pp. 5–6), the token velocity `v ≥ 1` (pp. 8–9), and the iso-elastic forms of §5 (p. 10).

**Formalization Note.**
* From §5 on (p. 10) the paper assumes `d(e,q) = e^a q^{-b}` with `0 < a < b < 1`,
  `s(q) = m q^n` with `m, n ≥ 0`, `C(Q) = K Q^k` with `k > (1 - b)/(1 - a)`; these are the
  fields of `Standing`, together with the printed `v ≥ 1` (p. 9).
* `Standing` adds `0 < δ < 1`, `0 ≤ c`, `0 < γ`, `0 ≤ K`, which the paper never states but uses
  throughout (δ is a discount factor, c a cost of joining, γe the cost of effort, C(Q) a cost).
* Powers are `Real.rpow`. Lean's convention `0 ^ y = 0` for `y ≠ 0` gives `d(e, 0) = 0` (the
  paper's `q^{-b}` is `+∞` there), `Fe 0 Q = Fe e 0 = 0` and `de 0 Q = 0`. These boundary values
  only matter at `Q = 0` or `e = 0`, which the programs exclude (directly, or because `γ > 0`).
* The partial derivatives `F_e`, `d_e` are defined by their closed forms under §5:
  `F_e(e,Q) = a e^{a-1} Q^{1-b}` and `d_e(e,Q) = a e^{a-1} Q^{-b}`; the helper theorems
  `Fe_hasDerivAt` and `de_hasDerivAt` state that they are the derivatives in `e` for `e, Q > 0`.
-/

namespace PlatformToken.SmallCost

/-- The parameters of the iso-elastic model of §5 (p. 10): demand exponents `a, b`, supply
`s(q) = m q^n`, capacity cost `C(Q) = K Q^k`, cost of joining `c`, effort cost `γ`, discount
factor `δ`, token velocity `v`. -/
structure Params where
  a : ℝ
  b : ℝ
  m : ℝ
  n : ℝ
  K : ℝ
  k : ℝ
  c : ℝ
  γ : ℝ
  δ : ℝ
  v : ℝ

/-- The standing assumptions: §5 (p. 10) `0 < a < b < 1`, `m, n ≥ 0`, `k > (1 - b)/(1 - a)`,
the token velocity `v ≥ 1` (p. 9), and the disclosed additions `0 < δ < 1`, `0 ≤ c`, `0 < γ`,
`0 ≤ K`. -/
structure Params.Standing (p : Params) : Prop where
  a_pos : 0 < p.a
  a_lt_b : p.a < p.b
  b_lt_one : p.b < 1
  m_nonneg : 0 ≤ p.m
  n_nonneg : 0 ≤ p.n
  K_nonneg : 0 ≤ p.K
  k_gt : (1 - p.b) / (1 - p.a) < p.k
  one_le_v : 1 ≤ p.v
  δ_pos : 0 < p.δ
  δ_lt_one : p.δ < 1
  c_nonneg : 0 ≤ p.c
  γ_pos : 0 < p.γ

/-- The same parameters with the capacity-cost scale replaced by `K` (Proposition 2 varies `K`
with everything else fixed). -/
def withK (p : Params) (K : ℝ) : Params := { p with K := K }

/-- Inverse demand `d(e,q) = e^a q^{-b}` (§5, p. 10). -/
noncomputable def d (p : Params) (e q : ℝ) : ℝ := e ^ p.a * q ^ (-p.b)

/-- Supply curve `s(q) = m q^n` (§5, p. 10). -/
noncomputable def s (p : Params) (q : ℝ) : ℝ := p.m * q ^ p.n

/-- Capacity investment cost `C(Q) = K Q^k` (§5, p. 10). -/
noncomputable def Ccap (p : Params) (Q : ℝ) : ℝ := p.K * Q ^ p.k

/-- The surplus `F(e,q) = q (d(e,q) - s(q))`, (8), p. 6. -/
noncomputable def F (p : Params) (e q : ℝ) : ℝ := q * (d p e q - s p q)

/-- The partial derivative `F_e(e,Q) = a e^{a-1} Q^{1-b}` of (8) in `e`, in closed form. -/
noncomputable def Fe (p : Params) (e Q : ℝ) : ℝ := p.a * e ^ (p.a - 1) * Q ^ (1 - p.b)

/-- The partial derivative `d_e(e,Q) = a e^{a-1} Q^{-b}` of the demand in `e`, in closed form. -/
noncomputable def de (p : Params) (e Q : ℝ) : ℝ := p.a * e ^ (p.a - 1) * Q ^ (-p.b)

/-- The entrepreneur's objective of (17), (33) and (37):
`F(e,Q)/(1 - δ) - cQ - C(Q) - γe`. -/
noncomputable def obj (p : Params) (e Q : ℝ) : ℝ :=
  F p e Q / (1 - p.δ) - p.c * Q - Ccap p Q - p.γ * e

/-- First-period revenue `π(x̄₁, q̄₁)` at effort `e` and capacity `Q`: the revenue (1),
`π(x, q) = x d(e,q) q`, evaluated at the fee (9), `x̄₁ = (d - s - c)/d`, and `q̄₁ = Q`. -/
noncomputable def pi1 (p : Params) (e Q : ℝ) : ℝ := (d p e Q - s p Q - p.c) * Q

/-- Revenue `π(x̄₂, q̄₂)` in every period `i ≥ 2`: (1) at the fee (10), `x̄ᵢ = (d - s)/d`,
and `q̄ᵢ = Q`. -/
noncomputable def pi2 (p : Params) (e Q : ℝ) : ℝ := (d p e Q - s p Q) * Q

end PlatformToken.SmallCost


