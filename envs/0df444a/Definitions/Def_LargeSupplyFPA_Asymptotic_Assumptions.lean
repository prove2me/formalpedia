-- Prove2me | Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions
-- name    : LargeSupplyFPA_Asymptotic_Assumptions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:02:48.961035+00:00
-- url     : https://prove2.me/theorems/b07394d6-1712-4c31-8e23-e23b0e943b5c
-- title:
--   Standing model of a sequence of auctions and Assumptions 1–4 (pp. 5, 6, 11, 15)
-- statement:
--   A **sequence of auctions** has, for every unit count $k$, an auction $A^{(k)}$ with $k$ units and $n(k)>k$ agents, value laws $V^{(k)}$ and a strategy profile $E^{(k)}$.
--
--   - **Assumption 1** (constants $H,\kappa$): every value lies in $[0,H]$ almost surely, and for every $\Delta>0$ and every $v\in[0,H-\Delta]$, $\Pr[V_i\in(v,v+\Delta)]>\kappa\Delta$.
--   - **Assumption 2** (no over-bidding): for every agent $i$ and every $v$ in the support of $V_i$, the bid drawn from $E_{i,v}$ is at most $v$ almost surely.
--   - **Over-bidding by at most $\omega$**: the same with $v+\omega$ in place of $v$.
--   - **Assumption 3**: there are $\omega^{(k)}>0$ with $\omega^{(k)}=o(k/n(k))$ such that $E^{(k)}$ over-bids by at most $\omega^{(k)}$, for every $k$.
--   - **Assumption 4** (one auction): no agent's marginal bid distribution has an atom.
--
--   **Formalization Note** Assumption 1(a) is printed as "$v_i\le H$ almost surely"; values are non-negative throughout the paper, and the definition records $V_i([0,H])=1$. Under Assumption 2 with non-negative bids this adds nothing. Positivity of $H$ and $\kappa$ is a separate hypothesis of each theorem. $o(\cdot)$ is `Asymptotics.IsLittleO` along `atTop`.
-- source:
--   Hartline, Shah, vonAllmen, Robust Analysis of First-Price Auctions with Large Supply, STOC 2027 submission (manuscript of November 3, 2026, sha256 2ad8363b…), p. 5 (§2 and Assumption 1), p. 6 (Assumption 2), p. 11 (Assumption 3), p. 15 (Assumption 4)

import Mathlib
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model

open MeasureTheory ProbabilityTheory Filter Asymptotics

namespace LargeSupplyFPA.Asymptotic

/-- The standing model of §2 for a sequence of auctions: the `k`-th auction `A^(k)` has `k`
units and `n k > k` agents, value laws `V k` and strategy profile `E k`. -/
def IsAuctionSequence (n : ℕ → ℕ) (V : ∀ k, Fin (n k) → Measure ℝ)
    (E : ∀ k, Fin (n k) → Kernel ℝ ℝ) : Prop :=
  (∀ k, k < n k) ∧ (∀ k, IsValueProfile (V k)) ∧ (∀ k, IsStrategyProfile (E k))

/-- Assumption 1 for one auction, with constants `H` and `κ`: (a) every value lies in
`[0, H]` almost surely; (b) for every `Δ > 0` and every `v ∈ [0, H - Δ]`,
`Pr[V_i ∈ (v, v + Δ)] > κ Δ`. -/
def Assumption1 {n : ℕ} (H κ : ℝ) (V : Fin n → Measure ℝ) : Prop :=
  ∀ i, V i (Set.Icc 0 H) = 1 ∧
    ∀ Δ : ℝ, 0 < Δ → ∀ v ∈ Set.Icc 0 (H - Δ), κ * Δ < (V i).real (Set.Ioo v (v + Δ))

/-- Assumption 2 (no over-bidding): for every agent `i` and every value `v` in the support of
`V i`, the bid drawn from `E i v` is at most `v` almost surely. -/
def NoOverbidding {n : ℕ} (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ) : Prop :=
  ∀ i, ∀ v ∈ (V i).support, E i v (Set.Iic v) = 1

/-- Over-bidding by at most `ω`: for every agent `i` and every value `v` in the support of
`V i`, the bid drawn from `E i v` is at most `v + ω` almost surely. -/
def OverbidAtMost {n : ℕ} (ω : ℝ) (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ) : Prop :=
  ∀ i, ∀ v ∈ (V i).support, E i v (Set.Iic (v + ω)) = 1

/-- Assumption 3: there are `ω^(k) > 0` with `ω^(k) = o(k / n(k))` such that the `k`-th
profile over-bids by at most `ω^(k)`. -/
def Assumption3 (n : ℕ → ℕ) (V : ∀ k, Fin (n k) → Measure ℝ)
    (E : ∀ k, Fin (n k) → Kernel ℝ ℝ) : Prop :=
  ∃ ω : ℕ → ℝ, (∀ k, 0 < ω k) ∧ (ω =o[atTop] fun k => (k : ℝ) / (n k : ℝ)) ∧
    ∀ k, OverbidAtMost (ω k) (V k) (E k)

/-- Assumption 4 for one auction: every agent's marginal bid distribution has no atoms. -/
def IsAtomless {n : ℕ} (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ) : Prop :=
  ∀ i, ∀ b : ℝ, marginalBid V E i {b} = 0

end LargeSupplyFPA.Asymptotic


