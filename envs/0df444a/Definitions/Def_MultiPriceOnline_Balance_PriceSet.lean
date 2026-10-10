-- Prove2me | Definitions.Def_MultiPriceOnline_Balance_PriceSet
-- name    : MultiPriceOnline_Balance_PriceSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:41:56.156981+00:00
-- url     : https://prove2.me/theorems/013de8ec-11f4-4195-bc82-7cb2387d0445
-- title:
--   §2–§2.1, pp. 11–14 — price sets with r⁽⁰⁾ = 0, booking limits (7), values σ of (8), L⁽ʲ⁾, F(𝒫) and G(𝒫)
-- statement:
--   This module fixes the price-set vocabulary of Ma and Simchi-Levi's multi-price online allocation model.
--
--   An item is sold at one of $m$ discrete prices $0<r^{(1)}<\dots<r^{(m)}$; by convention $r^{(0)}:=0$. The module defines:
--
--   1. **Price $j$ with $r^{(0)}=0$.** $\mathrm{pr}(r,j)=0$ if $j=0$ and $r^{(j)}$ otherwise.
--   2. **Price set.** $0<r^{(1)}$ and $r^{(j)}<r^{(j+1)}$ for $j=1,\dots,m-1$.
--   3. **Booking limits** (Proposition 1, (7)). Values $\alpha^{(1)},\dots,\alpha^{(m)}$ that are positive, sum to $1$, and satisfy, for $j=2,\dots,m$,
--   $$
--   1-e^{-\alpha^{(1)}}=\frac{1-e^{-\alpha^{(j)}}}{1-r^{(j-1)}/r^{(j)}}.
--   $$
--   4. **The values $\sigma$** (Proposition 1, (8)). Values $\sigma^{(1)},\dots,\sigma^{(m)}$ that are positive, sum to $1$, and satisfy $\sigma^{(1)}=\sigma^{(j)}/(1-r^{(j-1)}/r^{(j)})$ for $j=2,\dots,m$.
--   5. **Segment borders** (Definition 1). $L^{(j)}=\sum_{j'=1}^{j}\alpha^{(j')}$, so $L^{(0)}=0$.
--   6. **The ratios of Definition 2.** $F(\mathcal P)=1-e^{-\alpha^{(1)}}$ and $G(\mathcal P)=\sigma^{(1)}$.
--
--   Proposition 1 of the paper shows that for every price set both systems have exactly one solution. The booking limits drive the paper's algorithms, and $F$ and $G$ are the competitive ratios its main theorems are stated in.
--
--   **Formalization Note** Prices are a function $r:\mathbb N\to\mathbb R$ read at $1,\dots,m$; its values elsewhere are never used. The booking limits and $\sigma$ are predicates, not functions defined by choice: every theorem takes $\alpha$ (and $\sigma$) together with these predicates, and by the uniqueness in Proposition 1 they are then the paper's values. In (7) and (8) the denominator $1-r^{(j-1)}/r^{(j)}$ is positive for a price set, so the division is the paper's.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 11 (§2, r⁽⁰⁾ := 0), p. 13 (Proposition 1, (7)–(8)), p. 14 (Definitions 1–2)

import Mathlib

namespace MultiPriceOnline.Balance

/-- Price `j` of an item whose prices are `r 1, …, r m`, with the convention `r⁽⁰⁾ := 0`
(Ma–Simchi-Levi, arXiv:1905.04770v1, §2, p. 11). Prices are 1-based: only `j = 1, …, m` are
prices; `pr r 0 = 0`. -/
noncomputable def pr (r : ℕ → ℝ) (j : ℕ) : ℝ := if j = 0 then 0 else r j

/-- A price set `𝒫 = {r⁽¹⁾, …, r⁽ᵐ⁾}` with `0 < r⁽¹⁾ < … < r⁽ᵐ⁾` (§2, p. 11). The prices are read
at `1, …, m`; values of `r` elsewhere are irrelevant. -/
def IsPriceSet (m : ℕ) (r : ℕ → ℝ) : Prop :=
  0 < r 1 ∧ ∀ j, 1 ≤ j → j < m → r j < r (j + 1)

/-- The booking limits `α⁽¹⁾, …, α⁽ᵐ⁾` of Proposition 1 (p. 13): positive, summing to `1`, and
satisfying (7): `1 − e^{−α⁽¹⁾} = (1 − e^{−α⁽ʲ⁾}) / (1 − r⁽ʲ⁻¹⁾/r⁽ʲ⁾)` for `j = 2, …, m`.
Proposition 1 shows these values exist and are unique. -/
def IsBookingLimits (m : ℕ) (r α : ℕ → ℝ) : Prop :=
  (∀ j, 1 ≤ j → j ≤ m → 0 < α j) ∧ (∑ j ∈ Finset.Icc 1 m, α j) = 1 ∧
    ∀ j, 2 ≤ j → j ≤ m →
      1 - Real.exp (-α 1) = (1 - Real.exp (-α j)) / (1 - r (j - 1) / r j)

/-- The values `σ⁽¹⁾, …, σ⁽ᵐ⁾` of Proposition 1 (p. 13): positive, summing to `1`, and
satisfying (8): `σ⁽¹⁾ = σ⁽ʲ⁾ / (1 − r⁽ʲ⁻¹⁾/r⁽ʲ⁾)` for `j = 2, …, m`. -/
def IsBQLimits (m : ℕ) (r σ : ℕ → ℝ) : Prop :=
  (∀ j, 1 ≤ j → j ≤ m → 0 < σ j) ∧ (∑ j ∈ Finset.Icc 1 m, σ j) = 1 ∧
    ∀ j, 2 ≤ j → j ≤ m → σ 1 = σ j / (1 - r (j - 1) / r j)

/-- `L⁽ʲ⁾ = ∑_{j' = 1}^{j} α⁽ʲ'⁾` (Definition 1, p. 14); `L⁽⁰⁾ = 0`. -/
def Lsum (α : ℕ → ℝ) (j : ℕ) : ℝ := ∑ j' ∈ Finset.Icc 1 j, α j'

/-- `F(𝒫) = 1 − e^{−α⁽¹⁾}` (Definition 2, p. 14). -/
noncomputable def Fval (α : ℕ → ℝ) : ℝ := 1 - Real.exp (-α 1)

/-- `G(𝒫) = σ⁽¹⁾` (Definition 2, p. 14). -/
def Gval (σ : ℕ → ℝ) : ℝ := σ 1

end MultiPriceOnline.Balance


