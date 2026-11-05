-- Prove2me | Definitions.Def_BauerleRiederMDP_NoArbitrage_FinancialMarket
-- name    : BauerleRiederMDP_NoArbitrage_FinancialMarket
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:50.580009+00:00
-- url     : https://prove2.me/theorems/24ac3b36-7eb4-42a6-840f-a991f38d4258
-- title:
--   The $N$-period financial market with $d$ risky assets and a bond
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space with a filtration $(\mathcal F_n)_{n\ge0}$ and $\mathcal F_0=\{\emptyset,\Omega\}$. An **$N$-period financial market** with one riskless bond and $d$ risky assets consists of
--
--   1. deterministic interest rates $i_n\ge0$, $n=1,\dots,N$, where $i_{n+1}$ is the rate on $[n,n+1)$; the bond price is $S^0_0=1$, $S^0_{n+1}=S^0_n(1+i_{n+1})$;
--   2. deterministic initial prices $s^k_0>0$ and relative price changes $\tilde R_n=(\tilde R^1_n,\dots,\tilde R^d_n)$, random variables with $\tilde R^k_n>0$ $\mathbb P$-a.s. for $n=1,\dots,N$;
--   3. the price processes $S^k_0=s^k_0$, $S^k_{n+1}=S^k_n\tilde R^k_{n+1}$, which are $(\mathcal F_n)$-adapted for $n=0,\dots,N$.
--
--   This is the market model of Chapter 3 on which every portfolio problem of the book is built.
--
--   **Formalization Note** Time is indexed by $\mathbb N$; the data are constrained only for the times the book uses. $\mathbb R^d$ is `Fin d → ℝ`. The probability measure is a parameter of the structure; theorems assume it is a probability measure.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §3.1, pp.60–61 (PDF 74–75)

import Mathlib

open MeasureTheory

namespace BauerleRiederMDP.NoArbitrage

/-- The `N`-period financial market with `d` risky assets and one riskless bond
(Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §3.1, pp.60–61,
PDF 74–75).

All random variables live on a probability space `(Ω, 𝓕, ℙ)` with a filtration `(𝓕_n)` and
`𝓕_0 := {∅, Ω}`. The bond has deterministic interest rates `i_{n+1} ∈ ℝ₊` on `[n, n+1)`. The risky
asset `k` has the deterministic initial price `s^k_0` and the price process
`S^k_{n+1} = S^k_n R̃^k_{n+1}`, which is `(𝓕_n)`-adapted, and its relative price changes satisfy
`R̃^k_{n+1} > 0` `ℙ`-a.s. for `n = 0, …, N − 1`.

**Formalization Note** Time is indexed by `ℕ`; the fields constrain the data only for the times the
book uses (`1 ≤ n ≤ N` for `i_n`, `R̃_n`; `n ≤ N` for `S_n`), other values are unused. `ℝ^d` is
`Fin d → ℝ`. The price process `S^k_n = s^k_0 ∏_{t<n} R̃^k_{t+1}` is written out in `price_adapted`
(it is `FinancialMarket.price`). The relative price changes `R̃_n` are random variables, i.e.
`𝓕`-measurable (`Rt_meas`); adaptedness is required of the prices, as on p.61. The initial prices
are positive, as prices are on p.61 ("the stock price will stay positive with probability one").
The probability measure `ℙ` is a parameter; theorems add `[IsProbabilityMeasure P]`. -/
structure FinancialMarket (Ω : Type*) [m : MeasurableSpace Ω] (P : Measure Ω) (d : ℕ) where
  /-- The number of periods `N`. -/
  N : ℕ
  /-- The filtration `(𝓕_n)`. -/
  F : Filtration ℕ m
  /-- `𝓕_0 = {∅, Ω}`. -/
  F_zero : F 0 = ⊥
  /-- The deterministic interest rate `i_n` of the period `[n − 1, n)`. -/
  i : ℕ → ℝ
  /-- `i_n ∈ ℝ₊` for `n = 1, …, N`. -/
  i_nonneg : ∀ n, 1 ≤ n → n ≤ N → 0 ≤ i n
  /-- The deterministic initial prices `s^k_0` of the risky assets. -/
  s0 : Fin d → ℝ
  s0_pos : ∀ k, 0 < s0 k
  /-- The relative price changes `R̃_n = (R̃^1_n, …, R̃^d_n)` on `[n − 1, n)`. -/
  Rt : ℕ → Ω → Fin d → ℝ
  /-- Each `R̃_n` is a random variable. -/
  Rt_meas : ∀ n, 1 ≤ n → n ≤ N → Measurable (Rt n)
  /-- `R̃^k_n > 0` `ℙ`-a.s. for all `k` and `n = 1, …, N`. -/
  Rt_pos : ∀ n, 1 ≤ n → n ≤ N → ∀ᵐ ω ∂P, ∀ k, 0 < Rt n ω k
  /-- The price processes `S^k_n = s^k_0 R̃^k_1 ⋯ R̃^k_n` are `(𝓕_n)`-adapted. -/
  price_adapted : ∀ n, n ≤ N → ∀ k,
    Measurable[F n] (fun ω => s0 k * ∏ t ∈ Finset.range n, Rt (t + 1) ω k)

end BauerleRiederMDP.NoArbitrage


