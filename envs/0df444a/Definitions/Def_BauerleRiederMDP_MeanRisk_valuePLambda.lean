-- Prove2me | Definitions.Def_BauerleRiederMDP_MeanRisk_valuePLambda
-- name    : BauerleRiederMDP_MeanRisk_valuePLambda
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:28:44.432408+00:00
-- url     : https://prove2.me/theorems/b7ee342c-64e8-4d57-9a54-47838cb9e9e9
-- title:
--   Value of the Lagrange problem $P(\lambda)$
-- statement:
--   Throughout, the market is the binomial (Cox–Ross–Rubinstein) model of §4.7 with one stock and one bond with interest rate $i=0$: wealth $X_{n+1}=X_n+f_n(X_n)\,R_{n+1}$, where $f_n(x)\in\mathbb R$ is the amount invested in the stock and the relative risks $R_1,\dots,R_N$ are independent with $\mathbb P(R_n=u-1)=p\in(0,1)$, $\mathbb P(R_n=d-1)=1-p$. A policy $\pi=(f_0,\dots,f_{N-1})\in F^N$ is a sequence of measurable decision rules $f_n:\mathbb R\to\mathbb R$, and $X_0=x_0$. Assumption (FM) of the section is in force: (i) $0<d<1<u$ (no arbitrage; $d>0$ is the binomial model of §3.1), (iii) $0<x_0<\mu$, and the level is $\gamma\in(0,1)$. Write $q:=(1-d)/(u-d)\in(0,1)$ for the risk-neutral up-probability.
--
--   For $\lambda\ge0$ the **Lagrange problem** $P(\lambda)$ is $L_{x_0}(\pi,\lambda)\to\min$ over $\pi\in F^N$, and its value is
--
--   $$
--   \inf_{\pi\in F^N}L_{x_0}(\pi,\lambda)\in[-\infty,\infty).
--   $$
--
--   Proposition 4.7.2 computes it.
--
--   **Formalization Note** The infimum is taken in the extended reals over all measurable Markov policies, so the value $-\infty$ is `⊥`.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.7, problem P(λ), p.128 (PDF p.142); Proposition 4.7.2, p.129 (PDF p.143)

import Mathlib
import Definitions.Def_BauerleRiederMDP_MeanRisk_lagrangian

open MeasureTheory

namespace BauerleRiederMDP.MeanRisk

/-- The value `inf_{π ∈ F^N} L_{x₀}(π, λ)` of the Lagrange problem `P(λ)`, Bäuerle & Rieder (2011),
§4.7, p.128 (PDF 142) and Proposition 4.7.2, p.129 (PDF 143).

**Formalization Note.** The infimum is taken in `EReal` over all measurable Markov policies
(`IsAdmissible 0`), so that the book's value `−∞` is `⊥`. -/
noncomputable def valuePLambda {Ω : Type*} [MeasurableSpace Ω]
    (M : MDPFinance.MeanVariance.MeanRiskMarket Ω) (lam : ℝ) : EReal :=
  ⨅ π ∈ {π : ℕ → ℝ → ℝ | M.IsAdmissible 0 π}, ((lagrangian M π lam : ℝ) : EReal)

end BauerleRiederMDP.MeanRisk


