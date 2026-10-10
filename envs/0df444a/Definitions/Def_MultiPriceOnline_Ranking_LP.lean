-- Prove2me | Definitions.Def_MultiPriceOnline_Ranking_LP
-- name    : MultiPriceOnline_Ranking_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:42:35.564718+00:00
-- url     : https://prove2.me/theorems/bdd52dd0-58f9-41df-b7c5-8ccab1a0535f
-- title:
--   (5) and (19), pp. 11–12, 19 — the revenue LP of a setup and arrival sequence, and its dual
-- statement:
--   A firm sells $n$ items to $T$ customers who arrive one at a time. Item $i$ has a starting inventory $k_i\in\mathbb N$ and $m_i$ prices $r_i^{(1)}<\dots<r_i^{(m_i)}$; customer $t$ buys item $i$ at price $j$ with probability $p^{(j)}_{t,i}$. The **LP (5)** of the setup and arrival sequence, in variables $x^{(j)}_{t,i}$, is
--   $$\max\ \sum_{t=1}^T\sum_{i=1}^n\sum_{j=1}^{m_i}p^{(j)}_{t,i}\,r_i^{(j)}\,x^{(j)}_{t,i}$$
--   subject to
--   1. (5b) $\sum_{t=1}^T\sum_{j=1}^{m_i}p^{(j)}_{t,i}x^{(j)}_{t,i}\le k_i$ for every item $i$;
--   2. (5c) $\sum_{i=1}^n\sum_{j=1}^{m_i}x^{(j)}_{t,i}\le 1$ for every customer $t$;
--   3. (5d) $x^{(j)}_{t,i}\ge 0$.
--
--   Its **dual (19)**, in variables $y_i$ and $z_t$, minimizes $\sum_{i=1}^n k_iy_i+\sum_{t=1}^T z_t$ (19a) subject to
--   $$p^{(j)}_{t,i}\,y_i+z_t\ \ge\ p^{(j)}_{t,i}\,r_i^{(j)}\qquad t\in[T],\ i\in[n],\ j\in[m_i]\quad\text{(19b)},$$
--   and $y_i,z_t\ge 0$ (19c).
--
--   The optimal value $\mathrm{OPT}$ of (5) is the benchmark of the competitive ratio (6); every feasible solution of (19) bounds it from above, which is how the competitive analysis of Multi-price Ranking is carried out.
--
--   **Formalization Note** Items are indexed by `Fin n` and customers by `Fin T`, both 0-based (the paper's item $i$ is index $i-1$). Prices are 1-based inside an item: the sums over $j$ run over $\{1,\dots,m_i\}$, and the data $p$, $r$, $x$ are functions of $j\in\mathbb N$ whose values outside $[1,m_i]$ are never read. The objective and feasibility predicates are defined separately; the competitive ratio is later stated against every feasible $x$, so no supremum is formed.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, pp. 11–12, (5a)–(5d); p. 19, (19a)–(19c)

import Mathlib

namespace MultiPriceOnline.Ranking

/-! The LP (5) of Ma–Simchi-Levi (arXiv:1905.04770v1, pp. 11–12) and its dual (19) (p. 19).

Items are `Fin n` (the paper's item `i` is index `i - 1`), customers are `Fin T` (customer `t`
is index `t - 1`). Prices inside item `i` are 1-based: price `j ∈ {1, …, m i}`. The data
`p t i j` is the probability `p_{t,i}^{(j)}` and `r i j` is the price `r_i^{(j)}`; values at
`j = 0` or `j > m i` are never read. -/

/-- Objective (5a): `∑_t ∑_i ∑_{j=1}^{m_i} p_{t,i}^{(j)} r_i^{(j)} x_{t,i}^{(j)}`. -/
def lpObj {n T : ℕ} (m : Fin n → ℕ) (r : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (x : Fin T → Fin n → ℕ → ℝ) : ℝ :=
  ∑ t, ∑ i, ∑ j ∈ Finset.Icc 1 (m i), p t i j * r i j * x t i j

/-- Feasibility for the LP (5): the inventory constraints (5b), the one-offer-per-customer
constraints (5c) and nonnegativity (5d), for inventories `k`. -/
def LPFeasible {n T : ℕ} (k : Fin n → ℕ) (m : Fin n → ℕ) (p : Fin T → Fin n → ℕ → ℝ)
    (x : Fin T → Fin n → ℕ → ℝ) : Prop :=
  (∀ i, ∑ t, ∑ j ∈ Finset.Icc 1 (m i), p t i j * x t i j ≤ (k i : ℝ)) ∧
  (∀ t, ∑ i, ∑ j ∈ Finset.Icc 1 (m i), x t i j ≤ 1) ∧
  (∀ t i j, 1 ≤ j → j ≤ m i → 0 ≤ x t i j)

/-- Objective (19a) of the dual LP: `∑_i k_i y_i + ∑_t z_t`. -/
def dualObj {n T : ℕ} (k : Fin n → ℕ) (y : Fin n → ℝ) (z : Fin T → ℝ) : ℝ :=
  ∑ i, (k i : ℝ) * y i + ∑ t, z t

/-- Feasibility for the dual LP (19): the constraints (19b)
`p_{t,i}^{(j)} y_i + z_t ≥ p_{t,i}^{(j)} r_i^{(j)}` for all `t, i` and `j ∈ [m_i]`, and (19c)
`y, z ≥ 0`. -/
def DualFeasible {n T : ℕ} (m : Fin n → ℕ) (r : Fin n → ℕ → ℝ) (p : Fin T → Fin n → ℕ → ℝ)
    (y : Fin n → ℝ) (z : Fin T → ℝ) : Prop :=
  (∀ t i j, 1 ≤ j → j ≤ m i → p t i j * r i j ≤ p t i j * y i + z t) ∧
  (∀ i, 0 ≤ y i) ∧ (∀ t, 0 ≤ z t)

end MultiPriceOnline.Ranking


