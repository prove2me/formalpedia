-- Prove2me | Definitions.Def_BauerleRiederMDP_MeanRisk_valueMR
-- name    : BauerleRiederMDP_MeanRisk_valueMR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:28:04.138079+00:00
-- url     : https://prove2.me/theorems/62d65363-7e7e-41ae-954e-3ab7b83386e3
-- title:
--   Value $V_{MR}(x_0)$ of the mean-risk problem (MR)
-- statement:
--   Throughout, the market is the binomial (Cox–Ross–Rubinstein) model of §4.7 with one stock and one bond with interest rate $i=0$: wealth $X_{n+1}=X_n+f_n(X_n)\,R_{n+1}$, where $f_n(x)\in\mathbb R$ is the amount invested in the stock and the relative risks $R_1,\dots,R_N$ are independent with $\mathbb P(R_n=u-1)=p\in(0,1)$, $\mathbb P(R_n=d-1)=1-p$. A policy $\pi=(f_0,\dots,f_{N-1})\in F^N$ is a sequence of measurable decision rules $f_n:\mathbb R\to\mathbb R$, and $X_0=x_0$. Assumption (FM) of the section is in force: (i) $0<d<1<u$ (no arbitrage; $d>0$ is the binomial model of §3.1), (iii) $0<x_0<\mu$, and the level is $\gamma\in(0,1)$. Write $q:=(1-d)/(u-d)\in(0,1)$ for the risk-neutral up-probability.
--
--   The **mean-risk problem** (MR) is
--
--   $$
--   \mathrm{AVaR}^\pi_{x_0,\gamma}(X_N)\to\min,\qquad \mathbb E^\pi_{x_0}[X_N]\ge\mu,\qquad \pi\in F^N,
--   $$
--
--   where $\mathrm{AVaR}^\pi_{x_0,\gamma}(X_N)$ is the Average-Value-at-Risk at level $\gamma$ of the terminal wealth under $\pi$ from $x_0$. Its value $V_{MR}(x_0)\in[-\infty,+\infty]$ is the infimum of $\mathrm{AVaR}^\pi_{x_0,\gamma}(X_N)$ over all admissible $\pi$, those with $\mathbb E^\pi_{x_0}[X_N]\ge\mu$.
--
--   This is the quantity computed by Theorems 4.7.3 and 4.7.4.
--
--   **Formalization Note** The market, the policies, the terminal wealth and its expectation are those of the published definition `MDPFinance_MeanVariance_MeanRiskMarket` (a policy is `π : ℕ → ℝ → ℝ`, with `π n` used at time `n`, measurable for `n < N`). The infimum is taken in the extended reals: $-\infty$ is `⊥`, and an empty admissible set gives $+\infty$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.7, problem (MR), p.125 (PDF p.139)

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MeanRiskMarket
import Definitions.Def_BauerleRiederMDP_MeanRisk_AVaR

open MeasureTheory

namespace BauerleRiederMDP.MeanRisk

/-- The value `V_MR(x₀)` of the mean-risk problem (MR), Bäuerle & Rieder (2011), §4.7, p.125
(PDF 139):
`AVaR^π_{x₀,γ}(X_N) → min`, `𝔼^π_{x₀}[X_N] ≥ μ`, `π ∈ F^N`.

**Formalization Note.** The binomial market, Markov policies `π = (f₀, …, f_{N−1}) ∈ F^N`
(measurable `f_n : ℝ → ℝ`, encoded as `π : ℕ → ℝ → ℝ` with `π n` used at time `n`), the terminal
wealth `X_N` and `𝔼^π_{x₀}[X_N]` are those of the published bundle
`MDPFinance.MeanVariance.MeanRiskMarket`. `AVaR` is the book's quantile integral (`AVaR`). The value
is an infimum in `EReal`: `⊥` is the book's `−∞` and `⊤` (empty feasible set) its `+∞` (p.126). -/
noncomputable def valueMR {Ω : Type*} [MeasurableSpace Ω]
    (M : MDPFinance.MeanVariance.MeanRiskMarket Ω) : EReal :=
  ⨅ π ∈ {π : ℕ → ℝ → ℝ | M.IsAdmissible 0 π ∧ M.μ ≤ M.meanXN π},
    ((AVaR M.measIP M.γ (M.terminalWealth π M.N 0 M.x0) : ℝ) : EReal)

end BauerleRiederMDP.MeanRisk


