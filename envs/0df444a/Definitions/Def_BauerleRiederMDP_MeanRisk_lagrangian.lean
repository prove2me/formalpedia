-- Prove2me | Definitions.Def_BauerleRiederMDP_MeanRisk_lagrangian
-- name    : BauerleRiederMDP_MeanRisk_lagrangian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:28:01.445717+00:00
-- url     : https://prove2.me/theorems/9351142d-1395-4c64-ab14-434eb6e3947e
-- title:
--   Lagrange function $L_{x_0}(\pi,\lambda)$ of (MR)
-- statement:
--   Throughout, the market is the binomial (Cox–Ross–Rubinstein) model of §4.7 with one stock and one bond with interest rate $i=0$: wealth $X_{n+1}=X_n+f_n(X_n)\,R_{n+1}$, where $f_n(x)\in\mathbb R$ is the amount invested in the stock and the relative risks $R_1,\dots,R_N$ are independent with $\mathbb P(R_n=u-1)=p\in(0,1)$, $\mathbb P(R_n=d-1)=1-p$. A policy $\pi=(f_0,\dots,f_{N-1})\in F^N$ is a sequence of measurable decision rules $f_n:\mathbb R\to\mathbb R$, and $X_0=x_0$. Assumption (FM) of the section is in force: (i) $0<d<1<u$ (no arbitrage; $d>0$ is the binomial model of §3.1), (iii) $0<x_0<\mu$, and the level is $\gamma\in(0,1)$. Write $q:=(1-d)/(u-d)\in(0,1)$ for the risk-neutral up-probability.
--
--   The **Lagrange function** of (MR) is
--
--   $$
--   L_{x_0}(\pi,\lambda):=\mathrm{AVaR}^\pi_{x_0,\gamma}(X_N)+\lambda\big(\mu-\mathbb E^\pi_{x_0}[X_N]\big),\qquad \lambda\ge 0 .
--   $$
--
--   The value of (MR) is $\inf_{\pi}\sup_{\lambda\ge0}L_{x_0}(\pi,\lambda)$; the section solves the dual problem $\sup_{\lambda\ge0}\inf_\pi L_{x_0}(\pi,\lambda)$ first.
--
--   **Formalization Note** Defined for every real $\lambda$; every statement using it takes $\lambda\ge0$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.7, p.126 (PDF p.140)

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MeanRiskMarket
import Definitions.Def_BauerleRiederMDP_MeanRisk_AVaR

open MeasureTheory

namespace BauerleRiederMDP.MeanRisk

/-- The Lagrange function of (MR), Bäuerle & Rieder (2011), §4.7, p.126 (PDF 140):
`L_{x₀}(π, λ) := AVaR^π_{x₀,γ}(X_N) + λ(μ − 𝔼^π_{x₀}[X_N])`, `λ ≥ 0`.

**Formalization Note.** Defined for every real `λ`; the book and every statement using it take
`λ ≥ 0`. Policies, `X_N` and `𝔼^π_{x₀}` are those of `MDPFinance.MeanVariance.MeanRiskMarket`. -/
noncomputable def lagrangian {Ω : Type*} [MeasurableSpace Ω]
    (M : MDPFinance.MeanVariance.MeanRiskMarket Ω) (π : ℕ → ℝ → ℝ) (lam : ℝ) : ℝ :=
  AVaR M.measIP M.γ (M.terminalWealth π M.N 0 M.x0) + lam * (M.μ - M.meanXN π)

end BauerleRiederMDP.MeanRisk


