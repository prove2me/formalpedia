-- Prove2me | Definitions.Def_MechanismDesign_Dynamic_RepeatedSale
-- name    : MechanismDesign_Dynamic_RepeatedSale
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T05:38:26.785459+00:00
-- url     : https://prove2.me/theorems/d39d5ee6-b140-4b60-9d70-d0402338ccfe
-- title:
--   Dynamic allocations: $T$-period direct mechanisms with a fixed valuation, discounting, incentive compatibility, individual rationality
-- statement:
--   This file sets up §11.3 (pp.228–230). In each period $\tau=1,\dots,T$ a seller can sell one indivisible good to a buyer whose valuation $\theta\in[\underline\theta,\bar\theta]$, $0\le\underline\theta<\bar\theta$, does not change over time; the seller's belief about $\theta$ has distribution function $F$ and density $f>0$ as in Chapter 2. Seller and buyer discount with the common factor $\delta\in[0,1)$.
--
--   1. A (dynamic) **direct mechanism** (Definition 11.4) is $q=(q_1,\dots,q_T):[\underline\theta,\bar\theta]\to[0,1]^T$ and $t=(t_1,\dots,t_T):[\underline\theta,\bar\theta]\to\mathbb R^T$. The buyer's utility is
--   $$u(\theta)=\sum_{\tau=1}^{T}\delta^{\tau-1}\bigl[\theta q_\tau(\theta)-t_\tau(\theta)\bigr].$$
--   2. It is **incentive-compatible** (Definition 11.5) if $u(\theta)\ge\sum_{\tau=1}^{T}\delta^{\tau-1}[\theta q_\tau(\theta')-t_\tau(\theta')]$ for all $\theta,\theta'$, and **individually rational** (Definition 11.6) if $u(\theta)\ge0$ for all $\theta$.
--   3. The seller's expected revenue is $\int_{\underline\theta}^{\bar\theta}\sum_{\tau=1}^{T}\delta^{\tau-1}t_\tau(\theta)f(\theta)\,d\theta$.
--   4. The **repeated posted price** at $p^*$ uses in every period the static posted-price mechanism $(\bar q^s,\bar t^s)$: $\bar q^s(\theta)=1$, $\bar t^s(\theta)=p^*$ if $\theta\ge p^*$, and $\bar q^s(\theta)=0$, $\bar t^s(\theta)=0$ if $\theta<p^*$.
--
--   **Formalization Note** Periods are indexed by $k\in\{0,\dots,T-1\}$ with $k=\tau-1$. Admissibility adds measurability of every $q_\tau$, $t_\tau$. The Chapter 2 distribution is restated here rather than imported.
-- source:
--   Krähmer & Strausz, Ch. 11 in Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.228–229, §11.3, Definitions 11.4–11.6, the mechanism (q̄ˢ, t̄ˢ) (p.229)

import Mathlib

/-!
# Dynamic allocations: selling in `T` periods to a buyer with a fixed valuation
(Krähmer & Strausz, Ch. 11 in Börgers, §11.3, pp.228–230)

In each period `τ = 1, …, T` the seller can sell one indivisible good to a buyer whose valuation
`θ ∈ [θ̲, θ̄]` does not change over time. Seller and buyer discount with the common factor
`δ ∈ [0, 1)`. Periods are indexed by `k : Fin T`, `k = τ − 1`, so the discount weight
`δ^{τ−1}` is `δ ^ k`.
-/

namespace MechanismDesign.Dynamic

open MeasureTheory

/-- The seller's belief about the buyer's valuation, as in Chapter 2 (§2.2, p.7): a density
`f > 0` on `[θ̲, θ̄]`, `0 ≤ θ̲ < θ̄`, integrable with total mass `1`, and its cumulative
distribution function `F(θ) = ∫_{θ̲}^{θ} f(x) dx` on `[θ̲, θ̄]`. -/
structure ValuationDist (θlo θhi : ℝ) where
  /-- The density `f`. -/
  f : ℝ → ℝ
  /-- The cumulative distribution function `F`. -/
  F : ℝ → ℝ
  lo_nonneg : 0 ≤ θlo
  lo_lt_hi : θlo < θhi
  f_pos : ∀ θ ∈ Set.Icc θlo θhi, 0 < f θ
  f_integrable : IntervalIntegrable f volume θlo θhi
  f_total : ∫ x in θlo..θhi, f x = 1
  F_eq : ∀ θ ∈ Set.Icc θlo θhi, F θ = ∫ x in θlo..θ, f x

/-- A (dynamic) **direct mechanism** with `T` periods (Definition 11.4, pp.228–229):
`q k θ = q_{k+1}(θ) ∈ [0, 1]`, the probability that the buyer who reports `θ` obtains the good
in period `k + 1`, and `t k θ = t_{k+1}(θ)`, her payment in that period. -/
structure RepMechanism (T : ℕ) (θlo θhi : ℝ) where
  /-- `q k θ = q_{k+1}(θ)`. -/
  q : Fin T → ℝ → ℝ
  /-- `t k θ = t_{k+1}(θ)`. -/
  t : Fin T → ℝ → ℝ

namespace RepMechanism

variable {T : ℕ} {θlo θhi : ℝ}

/-- Admissibility: `q_τ(θ) ∈ [0, 1]` on `[θ̲, θ̄]` (Definition 11.4), and every `q_τ`, `t_τ` is
measurable (the measurability the book omits). -/
def Admissible (m : RepMechanism T θlo θhi) : Prop :=
  (∀ k, ∀ θ ∈ Set.Icc θlo θhi, m.q k θ ∈ Set.Icc (0 : ℝ) 1) ∧
  ∀ k, Measurable (m.q k) ∧ Measurable (m.t k)

/-- The discounted payoff of type `θ` who reports `θ′`:
`∑_{τ=1}^{T} δ^{τ−1} [θ q_τ(θ′) − t_τ(θ′)]`. -/
def payoff (δ : ℝ) (m : RepMechanism T θlo θhi) (θ θ' : ℝ) : ℝ :=
  ∑ k : Fin T, δ ^ (k : ℕ) * (θ * m.q k θ' - m.t k θ')

/-- `u(θ) = ∑_{τ=1}^{T} δ^{τ−1} [θ q_τ(θ) − t_τ(θ)]` (p.229). -/
def u (δ : ℝ) (m : RepMechanism T θlo θhi) (θ : ℝ) : ℝ :=
  m.payoff δ θ θ

/-- **Incentive compatibility** (Definition 11.5, p.229): `u(θ) ≥ ∑_{τ} δ^{τ−1}[θ q_τ(θ′) −
t_τ(θ′)]` for all `θ, θ′ ∈ [θ̲, θ̄]`. -/
def IsIC (δ : ℝ) (m : RepMechanism T θlo θhi) : Prop :=
  ∀ θ ∈ Set.Icc θlo θhi, ∀ θ' ∈ Set.Icc θlo θhi, m.payoff δ θ θ' ≤ m.u δ θ

/-- **Individual rationality** (Definition 11.6, p.229): `u(θ) ≥ 0` for all `θ ∈ [θ̲, θ̄]`. -/
def IsIR (δ : ℝ) (m : RepMechanism T θlo θhi) : Prop :=
  ∀ θ ∈ Set.Icc θlo θhi, 0 ≤ m.u δ θ

/-- The seller's expected discounted revenue
`∫_{θ̲}^{θ̄} ∑_{τ=1}^{T} δ^{τ−1} t_τ(θ) f(θ) dθ` (p.230). -/
noncomputable def revenue (D : ValuationDist θlo θhi) (δ : ℝ) (m : RepMechanism T θlo θhi) :
    ℝ :=
  ∫ θ in θlo..θhi, (∑ k : Fin T, δ ^ (k : ℕ) * m.t k θ) * D.f θ

end RepMechanism

/-- The repetition of the static posted-price mechanism `(q̄ˢ, t̄ˢ)` at price `p*` (p.229):
in every period, `q̄ˢ(θ) = 1` and `t̄ˢ(θ) = p*` if `θ ≥ p*`, and `q̄ˢ(θ) = 0`, `t̄ˢ(θ) = 0` if
`θ < p*`. -/
noncomputable def repeatedPostedPrice (T : ℕ) (θlo θhi pstar : ℝ) : RepMechanism T θlo θhi where
  q _ θ := if pstar ≤ θ then 1 else 0
  t _ θ := if pstar ≤ θ then pstar else 0

end MechanismDesign.Dynamic


