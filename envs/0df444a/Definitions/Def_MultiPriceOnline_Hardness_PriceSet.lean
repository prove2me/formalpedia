-- Prove2me | Definitions.Def_MultiPriceOnline_Hardness_PriceSet
-- name    : MultiPriceOnline_Hardness_PriceSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:42:59.307079+00:00
-- url     : https://prove2.me/theorems/063e82f7-fefa-446f-bb76-5f173ffd8044
-- title:
--   §2 and §5, pp. 11, 23 — price r⁽ʲ⁾ with r⁽⁰⁾ = 0, A_j (Definition 4) and the system (24) of Proposition 4
-- statement:
--   A **price set** with $m$ prices is a list $0 < r^{(1)} < r^{(2)} < \dots < r^{(m)}$; by convention $r^{(0)} := 0$.
--
--   The **booking limits** of Proposition 1 are the unique positive numbers $\alpha^{(1)},\dots,\alpha^{(m)}$ with $\sum_{j=1}^m \alpha^{(j)} = 1$ such that, for $j = 2,\dots,m$,
--
--   $$1 - e^{-\alpha^{(1)}} = \frac{1 - e^{-\alpha^{(j)}}}{1 - r^{(j-1)}/r^{(j)}}. \qquad (7)$$
--
--   The predicate `IsBookingLimits m r α` for these three conditions, the price set predicate and $F(\mathcal P) = 1 - e^{-\alpha^{(1)}}$ of Definition 2 come from the shared price-set module `MultiPriceOnline.Balance.PriceSet`, which this module imports. This module adds the following objects of §5.
--
--   For booking limits $\alpha$, Definition 4 sets $A_j := \sum_{\ell=j}^m \alpha^{(\ell)}$ for $j = 1, \dots, m+1$, so $A_1 = 1$ and $A_{m+1} = 0$.
--
--   The predicate `IsPhaseB m r α B` says that $B_1 = 1$ and that $B_2, \dots, B_m$ solve the system (24) of Proposition 4,
--
--   $$B_j\, r^{(j)} e^{-\alpha^{(j)}} = r^{(1)} e^{-\alpha^{(1)}}, \qquad j = 2, \dots, m.$$
--
--   In the counterexample of §5 the number $B_j$ is the fraction of customer groups in phases $j, \dots, m$.
--
--   **Formalization Note** Prices, booking limits and $B$ are functions $\mathbb N \to \mathbb R$ read at the 1-based indices $1,\dots,m$; `price r j` is $r^{(j)}$ with $r^{(0)} = 0$, a reducible alias of the shared `MultiPriceOnline.Balance.pr`. `IsPhaseB` records only the system (24) and $B_1 = 1$; the ordering $0 < B_m < \dots < B_2 < B_1$ is part of Proposition 4's conclusion, not of the predicate. The booking limits enter as a predicate rather than as a chosen function, because a definition cannot carry Proposition 1's existence proof; Proposition 1 makes the solution unique, so every statement is about the paper's $\alpha$. Equation (7) is written with the division as printed; strict monotonicity of the prices makes the denominator positive.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 11 (price sets), p. 13 Proposition 1 eq. (7), p. 23 Definition 4 and Proposition 4 eq. (24)

import Mathlib
import Definitions.Def_MultiPriceOnline_Balance_PriceSet

namespace MultiPriceOnline.Hardness

open Finset

/-- The price `r⁽ʲ⁾` with the paper's convention `r⁽⁰⁾ := 0` (p. 11): the shared
`MultiPriceOnline.Balance.pr`, under the name this mission's statements use. -/
noncomputable abbrev price (r : ℕ → ℝ) (j : ℕ) : ℝ := MultiPriceOnline.Balance.pr r j

/-- `A_j := ∑_{ℓ=j}^m α⁽ℓ⁾` (Definition 4, p. 23). -/
def Asum (m : ℕ) (α : ℕ → ℝ) (j : ℕ) : ℝ := ∑ l ∈ Icc j m, α l

/-- `B` is the solution of Proposition 4 (p. 23): `B 1 = 1` and the system (24),
`B_j r⁽ʲ⁾ e^{−α⁽ʲ⁾} = r⁽¹⁾ e^{−α⁽¹⁾}` for `j = 2, …, m`. Only `B 1, …, B m` matter; the paper's
`B_{m+1} = 0` (Definition 4) is used explicitly where it is needed. -/
def IsPhaseB (m : ℕ) (r : ℕ → ℝ) (α : ℕ → ℝ) (B : ℕ → ℝ) : Prop :=
  B 1 = 1 ∧ ∀ j : ℕ, 2 ≤ j → j ≤ m →
    B j * r j * Real.exp (-α j) = r 1 * Real.exp (-α 1)

end MultiPriceOnline.Hardness


