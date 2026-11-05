-- Prove2me | Definitions.Def_BauerleRiederMDP_MeanRisk_IsOptimalMR
-- name    : BauerleRiederMDP_MeanRisk_IsOptimalMR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:28:07.053893+00:00
-- url     : https://prove2.me/theorems/1fcbe384-bf80-4466-94cc-c9792c05977d
-- title:
--   Optimal policy for the mean-risk problem (MR)
-- statement:
--   Throughout, the market is the binomial (Cox–Ross–Rubinstein) model of §4.7 with one stock and one bond with interest rate $i=0$: wealth $X_{n+1}=X_n+f_n(X_n)\,R_{n+1}$, where $f_n(x)\in\mathbb R$ is the amount invested in the stock and the relative risks $R_1,\dots,R_N$ are independent with $\mathbb P(R_n=u-1)=p\in(0,1)$, $\mathbb P(R_n=d-1)=1-p$. A policy $\pi=(f_0,\dots,f_{N-1})\in F^N$ is a sequence of measurable decision rules $f_n:\mathbb R\to\mathbb R$, and $X_0=x_0$. Assumption (FM) of the section is in force: (i) $0<d<1<u$ (no arbitrage; $d>0$ is the binomial model of §3.1), (iii) $0<x_0<\mu$, and the level is $\gamma\in(0,1)$. Write $q:=(1-d)/(u-d)\in(0,1)$ for the risk-neutral up-probability.
--
--   A policy $\pi^*\in F^N$ is **optimal for (MR)** if it is admissible, $\mathbb E^{\pi^*}_{x_0}[X_N]\ge\mu$, and
--
--   $$
--   \mathrm{AVaR}^{\pi^*}_{x_0,\gamma}(X_N)\le \mathrm{AVaR}^{\pi}_{x_0,\gamma}(X_N)\quad\text{for every }\pi\in F^N\text{ with }\mathbb E^{\pi}_{x_0}[X_N]\ge\mu .
--   $$
--
--   An optimal policy attains the value $V_{MR}(x_0)$.
--
--   **Formalization Note** Policies are the measurable Markov policies of `MDPFinance_MeanVariance_MeanRiskMarket`; the Average-Value-at-Risk is the quantile integral of `AVaR`.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.7, problem (MR), p.125 (PDF p.139)

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MeanRiskMarket
import Definitions.Def_BauerleRiederMDP_MeanRisk_AVaR

open MeasureTheory

namespace BauerleRiederMDP.MeanRisk

/-- A policy `π*` is optimal for the mean-risk problem (MR), Bäuerle & Rieder (2011), §4.7, p.125
(PDF 139): it belongs to `F^N`, it is admissible for (MR) (`𝔼^{π*}_{x₀}[X_N] ≥ μ`), and its
`AVaR^{π*}_{x₀,γ}(X_N)` is no larger than that of any admissible `π ∈ F^N`.

**Formalization Note.** Policies are as in `valueMR` (bundle `MDPFinance.MeanVariance.MeanRiskMarket`);
`AVaR` is the book's quantile integral. -/
def IsOptimalMR {Ω : Type*} [MeasurableSpace Ω]
    (M : MDPFinance.MeanVariance.MeanRiskMarket Ω) (πstar : ℕ → ℝ → ℝ) : Prop :=
  M.IsAdmissible 0 πstar ∧ M.μ ≤ M.meanXN πstar ∧
    ∀ π : ℕ → ℝ → ℝ, M.IsAdmissible 0 π → M.μ ≤ M.meanXN π →
      AVaR M.measIP M.γ (M.terminalWealth πstar M.N 0 M.x0) ≤
        AVaR M.measIP M.γ (M.terminalWealth π M.N 0 M.x0)

end BauerleRiederMDP.MeanRisk


