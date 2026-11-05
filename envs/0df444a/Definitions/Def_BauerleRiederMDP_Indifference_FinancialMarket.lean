-- Prove2me | Definitions.Def_BauerleRiederMDP_Indifference_FinancialMarket
-- name    : BauerleRiederMDP_Indifference_FinancialMarket
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:13.808821+00:00
-- url     : https://prove2.me/theorems/4aa1f2cd-1b10-475c-aa2a-d8a8a4c447d6
-- title:
--   The $N$-period financial market of §3.1 and App. C.1
-- statement:
--   An $N$-period financial market with $d$ risky assets consists of a probability space $(\Omega,\mathcal F,\mathbb P)$ with a filtration $(\mathcal F_n)$, $\mathcal F_0=\{\emptyset,\Omega\}$, a bond $S^0_0=1$, $S^0_{n+1}=S^0_n(1+i_{n+1})$ with deterministic rates $i_{n+1}\in\mathbb R_+$, and risky assets $S^k_0=s^k_0$, $S^k_{n+1}=S^k_n\tilde R^k_{n+1}$. The price processes are adapted, $\tilde R^k_{n+1}>0$ almost surely, and $s^k_0$ is deterministic.
--
--   This is the market in which the no-arbitrage pricing theory of Appendix C.1 is stated.
--
--   **Formalization Note** Time is indexed by $\mathbb N$; only $n\le N$ carries meaning. The conditions $N>0$ and $s^k_0>0$ are the book's: a strategy has an initial portfolio, and prices stay positive (p.61).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §3.1, p.61 and App. C.1, p.365

import Mathlib

open MeasureTheory

namespace BauerleRiederMDP.Indifference

/-- The `N`-period financial market with `d` risky assets and one riskless bond of §3.1 and App. C.1
(Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §3.1, p.61, PDF 75
and App. C.1, p.365, PDF 370): a probability space with a filtration `(𝓕_n)`, `𝓕₀ = {∅, Ω}`,
deterministic interest rates `i_{n+1} ∈ ℝ₊`, and asset prices `S^k₀ = s^k₀`,
`S^k_{n+1} = S^k_n R̃^k_{n+1}` with `R̃^k_{n+1} > 0` `ℙ`-a.s., `(S^k_n)` adapted, `s^k₀` deterministic.

**Formalization Note.** The time index is `ℕ`; only `n ≤ N` (`1 ≤ n ≤ N` for `i` and `Rt`) carries
meaning. `0 < N` because a trading strategy has an initial portfolio `(φ⁰₀, φ₀)`, and `0 < s^k₀`
because `s^k₀` is a price: the book states that the prices stay positive (p.61). -/
structure FinancialMarket (Ω : Type*) [mΩ : MeasurableSpace Ω] (d N : ℕ) where
  /-- The probability measure `ℙ`. -/
  P : Measure Ω
  isProb : IsProbabilityMeasure P
  /-- The filtration `(𝓕_n)`. -/
  F : Filtration ℕ mΩ
  F_zero : ∀ A, MeasurableSet[F 0] A → A = ∅ ∨ A = Set.univ
  N_pos : 0 < N
  /-- The interest rates: `i n` is the rate `i_n` of the period `[n - 1, n)`. -/
  i : ℕ → ℝ
  i_nonneg : ∀ n, 1 ≤ n → n ≤ N → 0 ≤ i n
  /-- The relative price changes: `Rt n ω k` is `R̃^k_n(ω)`. -/
  Rt : ℕ → Ω → Fin d → ℝ
  Rt_pos : ∀ n, 1 ≤ n → n ≤ N → ∀ k, ∀ᵐ ω ∂P, 0 < Rt n ω k
  /-- The initial prices `s^k₀`. -/
  s₀ : Fin d → ℝ
  s₀_pos : ∀ k, 0 < s₀ k
  /-- The prices: `S n ω k` is `S^k_n(ω)`. -/
  S : ℕ → Ω → Fin d → ℝ
  S_zero : ∀ ω k, S 0 ω k = s₀ k
  S_succ : ∀ n, n < N → ∀ ω k, S (n + 1) ω k = S n ω k * Rt (n + 1) ω k
  S_adapted : ∀ n, n ≤ N → ∀ k, Measurable[F n] fun ω => S n ω k

namespace FinancialMarket

variable {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}

/-- The bond price `S⁰_n = ∏_{t=1}^n (1 + i_t)`, so `S⁰₀ = 1` and `S⁰_{n+1} = S⁰_n (1 + i_{n+1})`
(p.61, PDF 75). -/
noncomputable def S0 (M : FinancialMarket Ω d N) (n : ℕ) : ℝ :=
  ∏ t ∈ Finset.range n, (1 + M.i (t + 1))

end FinancialMarket

end BauerleRiederMDP.Indifference


