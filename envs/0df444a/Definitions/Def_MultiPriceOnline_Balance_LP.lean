-- Prove2me | Definitions.Def_MultiPriceOnline_Balance_LP
-- name    : MultiPriceOnline_Balance_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:41:55.881213+00:00
-- url     : https://prove2.me/theorems/9e41652f-ef23-47c6-8149-63b4ca992bf7
-- title:
--   (5) and (19), pp. 11–12 and 19 — the LP benchmark of the multi-price online allocation problem and its dual
-- statement:
--   This module defines the linear program (5) that benchmarks online algorithms in Ma and Simchi-Levi's model, and its dual (19).
--
--   There are items $i$ in a finite set, item $i$ with inventory $k_i$ and prices $r_i^{(1)},\dots,r_i^{(m_i)}$, and customers $t=1,\dots,T$. The number $p^{(j)}_{t,i}$ is the probability that customer $t$ buys item $i$ at price $j$. The LP (5) is
--   $$
--   \max\ \sum_{t=1}^T\sum_{i}\sum_{j=1}^{m_i}p^{(j)}_{t,i}r_i^{(j)}x^{(j)}_{t,i}
--   \quad\text{s.t.}\quad
--   \sum_{t=1}^T\sum_{j=1}^{m_i}p^{(j)}_{t,i}x^{(j)}_{t,i}\le k_i\ \ (5\mathrm b),\qquad
--   \sum_{i}\sum_{j=1}^{m_i}x^{(j)}_{t,i}\le 1\ \ (5\mathrm c),\qquad
--   x^{(j)}_{t,i}\ge 0\ \ (5\mathrm d).
--   $$
--   Its dual (19) is
--   $$
--   \min\ \sum_i k_iy_i+\sum_{t=1}^T z_t
--   \quad\text{s.t.}\quad
--   p^{(j)}_{t,i}y_i+z_t\ge p^{(j)}_{t,i}r_i^{(j)}\ \ (19\mathrm b),\qquad
--   y_i,\ z_t\ge 0\ \ (19\mathrm c).
--   $$
--   The module defines the objective (5a), feasibility for (5), the objective (19a) and feasibility for (19). The optimal value of (5) is the benchmark $\mathrm{OPT}(\mathcal S,\mathcal A)$ in the definition (6) of the competitive ratio, and the paper's primal–dual analysis bounds it through feasible solutions of (19).
--
--   **Formalization Note** Items form an arbitrary finite type; customers are indexed $0,\dots,T-1$ (customer $t$ of the paper is index $t-1$); prices are $1$-based. All arrays are read only at $j\in[1,m_i]$.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, pp. 11–12, (5a)–(5d); p. 19, (19a)–(19c)

import Mathlib

namespace MultiPriceOnline.Balance

/-! The LP (5) and its dual (19) of Ma–Simchi-Levi (arXiv:1905.04770v1, pp. 11–12 and 19), for a
finite item type `ι`. Customers are `Fin T` (customer `t` of the paper is index `t − 1`); prices of
item `i` are `j = 1, …, m i`. Arrays `p t i j` (purchase probabilities), `r i j` (prices) and
`x t i j` (LP variables) are read only at `j ∈ [1, m i]`. -/

variable {ι : Type*} [Fintype ι]

/-- The objective (5a): `∑_t ∑_i ∑_{j=1}^{mᵢ} p⁽ʲ⁾_{t,i} rᵢ⁽ʲ⁾ x⁽ʲ⁾_{t,i}`. -/
def lpObj (m : ι → ℕ) (r : ι → ℕ → ℝ) {T : ℕ} (p : Fin T → ι → ℕ → ℝ)
    (x : Fin T → ι → ℕ → ℝ) : ℝ :=
  ∑ t, ∑ i, ∑ j ∈ Finset.Icc 1 (m i), p t i j * r i j * x t i j

/-- Feasibility for the LP (5): (5b) `∑_t ∑_j p⁽ʲ⁾_{t,i} x⁽ʲ⁾_{t,i} ≤ kᵢ` for every item `i`,
(5c) `∑_i ∑_j x⁽ʲ⁾_{t,i} ≤ 1` for every customer `t`, and (5d) `x⁽ʲ⁾_{t,i} ≥ 0`. -/
def LPFeasible (k m : ι → ℕ) {T : ℕ} (p : Fin T → ι → ℕ → ℝ) (x : Fin T → ι → ℕ → ℝ) : Prop :=
  (∀ i, ∑ t, ∑ j ∈ Finset.Icc 1 (m i), p t i j * x t i j ≤ (k i : ℝ)) ∧
    (∀ t, ∑ i, ∑ j ∈ Finset.Icc 1 (m i), x t i j ≤ 1) ∧
    ∀ t i j, 1 ≤ j → j ≤ m i → 0 ≤ x t i j

/-- The dual objective (19a): `∑_i kᵢ yᵢ + ∑_t z_t`. -/
def dualObj (k : ι → ℕ) {T : ℕ} (y : ι → ℝ) (z : Fin T → ℝ) : ℝ :=
  ∑ i, (k i : ℝ) * y i + ∑ t, z t

/-- Feasibility for the dual (19): (19b) `p⁽ʲ⁾_{t,i} yᵢ + z_t ≥ p⁽ʲ⁾_{t,i} rᵢ⁽ʲ⁾` for all `t, i` and
`j ∈ [mᵢ]`, and (19c) `yᵢ, z_t ≥ 0`. -/
def DualFeasible (m : ι → ℕ) (r : ι → ℕ → ℝ) {T : ℕ} (p : Fin T → ι → ℕ → ℝ) (y : ι → ℝ)
    (z : Fin T → ℝ) : Prop :=
  (∀ t i j, 1 ≤ j → j ≤ m i → p t i j * r i j ≤ p t i j * y i + z t) ∧
    (∀ i, 0 ≤ y i) ∧ ∀ t, 0 ≤ z t

end MultiPriceOnline.Balance


