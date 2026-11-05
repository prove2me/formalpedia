-- Prove2me | Definitions.Def_BauerleRiederMDP_MeanRisk_IsOptimalPLambda
-- name    : BauerleRiederMDP_MeanRisk_IsOptimalPLambda
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:18.75381+00:00
-- url     : https://prove2.me/theorems/e460f2f3-a71c-421c-a41b-9288afd55ffb
-- title:
--   Optimal policy for the Lagrange problem $P(\lambda)$
-- statement:
--   Throughout, the market is the binomial (Cox–Ross–Rubinstein) model of §4.7 with one stock and one bond with interest rate $i=0$: wealth $X_{n+1}=X_n+f_n(X_n)\,R_{n+1}$, where $f_n(x)\in\mathbb R$ is the amount invested in the stock and the relative risks $R_1,\dots,R_N$ are independent with $\mathbb P(R_n=u-1)=p\in(0,1)$, $\mathbb P(R_n=d-1)=1-p$. A policy $\pi=(f_0,\dots,f_{N-1})\in F^N$ is a sequence of measurable decision rules $f_n:\mathbb R\to\mathbb R$, and $X_0=x_0$. Assumption (FM) of the section is in force: (i) $0<d<1<u$ (no arbitrage; $d>0$ is the binomial model of §3.1), (iii) $0<x_0<\mu$, and the level is $\gamma\in(0,1)$. Write $q:=(1-d)/(u-d)\in(0,1)$ for the risk-neutral up-probability.
--
--   A policy $\pi^*\in F^N$ is **optimal for** $P(\lambda)$ if $L_{x_0}(\pi^*,\lambda)\le L_{x_0}(\pi,\lambda)$ for every $\pi\in F^N$.
--
--   **Formalization Note** Policies are the measurable Markov policies of `MDPFinance_MeanVariance_MeanRiskMarket`.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.7, problem P(λ), p.128 (PDF p.142)

import Mathlib
import Definitions.Def_BauerleRiederMDP_MeanRisk_lagrangian

open MeasureTheory

namespace BauerleRiederMDP.MeanRisk

/-- A policy `π*` is optimal for the Lagrange problem `P(λ)`, Bäuerle & Rieder (2011), §4.7, p.128
(PDF 142): `π* ∈ F^N` and `L_{x₀}(π*, λ) ≤ L_{x₀}(π, λ)` for every `π ∈ F^N`.

**Formalization Note.** Policies are the measurable Markov policies of
`MDPFinance.MeanVariance.MeanRiskMarket` (`IsAdmissible 0`). -/
def IsOptimalPLambda {Ω : Type*} [MeasurableSpace Ω]
    (M : MDPFinance.MeanVariance.MeanRiskMarket Ω) (lam : ℝ) (πstar : ℕ → ℝ → ℝ) : Prop :=
  M.IsAdmissible 0 πstar ∧
    ∀ π : ℕ → ℝ → ℝ, M.IsAdmissible 0 π → lagrangian M πstar lam ≤ lagrangian M π lam

end BauerleRiederMDP.MeanRisk


