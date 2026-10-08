-- Prove2me | Definitions.Def_RevShareCoord_Competing_Game
-- name    : RevShareCoord_Competing_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T20:39:36.563398+00:00
-- url     : https://prove2.me/theorems/40b52e52-1b66-4687-b3c9-e0b1c5d4dcfd
-- title:
--   Sec. 3.2 — the competing-retailers quantity game: retailer, supplier and system profits, and Nash equilibrium in order quantities
-- statement:
--   A single supplier sells one product through $n$ locations $i = 1,\dots,n$, each run by an independent retailer. A **stocking profile** is a vector $\bar q = (q_1,\dots,q_n)$ of order quantities, and $R_i(\bar q)$ is the revenue earned at location $i$; it may depend on the quantities stocked at every location. The supplier produces at unit cost $c$.
--
--   The supplier offers retailer $i$ a **revenue-sharing contract** $(\phi, w_i)$: retailer $i$ pays the wholesale price $w_i$ per unit and keeps the fraction $\phi$ of its revenue, the supplier receiving the remaining $1-\phi$. The plain **wholesale-price contract** is the case $\phi = 1$. This definition introduces:
--
--   1. Retailer $i$'s profit
--   $$\pi_{r_i}(\bar q, \phi, \bar w) = \phi R_i(\bar q) - w_i q_i ,$$
--   which for $\phi = 1$ is the wholesale-price profit $\pi_{r_i}(\bar q, \bar w) = R_i(\bar q) - q_i w_i$.
--   2. The supplier's profit
--   $$\pi_s(\bar q, \phi, \bar w) = \sum_{i=1}^n \big((1-\phi) R_i(\bar q) + w_i q_i\big) - c \sum_{i=1}^n q_i ,$$
--   which for $\phi = 1$ is $\pi_s(\bar q, \bar w) = \sum_i (w_i - c) q_i$.
--   3. The integrated system profit $\Pi(\bar q) = R(\bar q) - c\sum_i q_i$, where $R(\bar q) = \sum_i R_i(\bar q)$.
--   4. A **Nash equilibrium in order quantities** under the contracts $(\phi, w_i)$: a profile $\bar q$ with every $q_i \ge 0$ such that no retailer $i$ can raise its own profit by changing its own quantity to any $x \ge 0$ while the other retailers keep theirs.
--
--   These are the objects in which the paper's coordination results for competing retailers are stated.
--
--   **Formalization Note** Locations are indexed by `Fin n`, a profile is a function `Fin n → ℝ`, and the revenue functions are `R : Fin n → (Fin n → ℝ) → ℝ`. A unilateral deviation of retailer $i$ to $x$ is `Function.update q i x`. Deviations range over all $x \ge 0$, not only over quantities satisfying a first-order condition.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), pp. 12–14 (PDF pp. 13–15), Section 3.2: R(q̄) = Σ R_i(q̄) (p. 12), Π(q̄^I) (p. 12), Nash equilibrium in order quantities (p. 13), π_{r_i}, π_s (p. 14)

import Mathlib

/-!
# The competing-retailers quantity game (Cachon–Lariviere, June 2000 working paper, Sec. 3.2)

A single supplier sells through `n` locations `i : Fin n`, each run by an independent retailer.
A stocking profile is `q : Fin n → ℝ` (the paper's `q̄ = {q₁, …, qₙ}`), and the revenue at
location `i` is `R i q` (the paper's `Rᵢ(q̄)`). The supplier offers retailer `i` a
revenue-sharing contract `(φ, wᵢ)`: retailer `i` pays `wᵢ` per unit and keeps the fraction `φ`
of its revenue. The wholesale-price contract is the case `φ = 1`.
-/

namespace RevShareCoord.Competing

open Finset

variable {n : ℕ}

/-- Retailer `i`'s profit under the revenue-sharing contract `(φ, w̄)` at the profile `q`:
`π_{rᵢ}(q̄, φ, w̄) = φ Rᵢ(q̄) − wᵢ qᵢ` (Sec. 3.2, p. 14). With `φ = 1` this is the
wholesale-price profit `π_{rᵢ}(q̄, w̄) = Rᵢ(q̄) − qᵢ wᵢ` (p. 14). -/
def retailerProfit (R : Fin n → (Fin n → ℝ) → ℝ) (φ : ℝ) (w : Fin n → ℝ)
    (q : Fin n → ℝ) (i : Fin n) : ℝ :=
  φ * R i q - w i * q i

/-- The supplier's profit under the revenue-sharing contracts `(φ, wᵢ)`: she receives
`wᵢ qᵢ` and `(1 − φ) Rᵢ(q̄)` from every retailer and pays `c` per unit produced,
`π_s(q̄, φ, w̄) = Σᵢ ((1 − φ) Rᵢ(q̄) + wᵢ qᵢ) − c Σᵢ qᵢ` (Sec. 3.2, p. 14). With `φ = 1` this is
the wholesale-price profit `π_s(q̄, w̄) = Σᵢ (wᵢ − c) qᵢ`. -/
def supplierProfit (R : Fin n → (Fin n → ℝ) → ℝ) (c φ : ℝ) (w : Fin n → ℝ)
    (q : Fin n → ℝ) : ℝ :=
  ∑ i, ((1 - φ) * R i q + w i * q i) - c * ∑ i, q i

/-- The integrated system profit `Π(q̄) = R(q̄) − c Σᵢ qᵢ` with `R(q̄) = Σᵢ Rᵢ(q̄)`
(Sec. 3.2, p. 12). -/
def systemProfit (R : Fin n → (Fin n → ℝ) → ℝ) (c : ℝ) (q : Fin n → ℝ) : ℝ :=
  ∑ i, R i q - c * ∑ i, q i

/-- A (pure-strategy) **Nash equilibrium in order quantities** of the retailers' game under the
contracts `(φ, wᵢ)` (Sec. 3.2, pp. 13–14): every quantity is nonnegative, and no retailer `i`
gains by changing its own quantity to any `x ≥ 0` while the other retailers keep theirs. -/
def IsNashEquilibrium (R : Fin n → (Fin n → ℝ) → ℝ) (φ : ℝ) (w : Fin n → ℝ)
    (q : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧
    ∀ (i : Fin n) (x : ℝ), 0 ≤ x →
      retailerProfit R φ w (Function.update q i x) i ≤ retailerProfit R φ w q i

end RevShareCoord.Competing


