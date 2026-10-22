-- Prove2me | Definitions.Def_RiskPostpone_Threshold_CVaR
-- name    : RiskPostpone_Threshold_CVaR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:08.740083+00:00
-- url     : https://prove2.me/theorems/6f8cb6e1-8e37-4ab8-86d1-bbaff56e33d0
-- title:
--   The Rockafellar–Uryasev maximization formula for the CVaR of a random profit (p. 7)
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a probability space, $X:\Omega\to\mathbb R$ a random profit and $\eta\in(0,1]$ a quantile level. The **conditional value-at-risk** of the profit $X$ at level $\eta$ is given by the Rockafellar–Uryasev maximization formula
--   $$
--   \mathrm{CVaR}_\eta(X)=\max_{v\in\mathbb R}\Big\{v+\frac1\eta\,\mathbb E\big[\min\{X-v,0\}\big]\Big\}.
--   $$
--
--   Applied to a profit rather than a loss, CVaR averages the lower $\eta$-tail of the profit: the smaller $\eta$, the more weight on low profit realizations, and $\eta=1$ gives the expectation. Every objective of the mission is a CVaR of this form; the value-at-risk $\mathrm{VaR}_\eta(X)=\inf\{v:\mu(X\le v)\ge\eta\}$ is the published `MultistageStochastic.valueAtRisk`.
--
--   **Formalization Note** CVaR is defined for an arbitrary measure $\mu$ on an arbitrary measurable space as the real supremum over $v\in\mathbb R$ of the bracket; the statements that use it assume $\mu$ is a probability measure. For an integrable $X$ and $0<\eta\le1$ the bracket is bounded above by $\mathbb E[X]$, so the supremum is genuine; for a non-integrable $X$ Lean's Bochner integral is $0$ and the value is meaningless, so every statement about a general $X$ assumes integrability.
-- source:
--   Kouvelis, Xiao and Yang, Role of Risk Aversion in Price Postponement under Supply Random Yield, accepted manuscript MS-OPM-18-01273.R2 (Management Science 67(8), 2021, doi:10.1287/mnsc.2020.3755), p. 7, the CVaR maximization formula

import Mathlib

open MeasureTheory

namespace RiskPostpone.Threshold

/-- The Rockafellar–Uryasev maximization formula for the conditional value-at-risk of a random
profit `X : Ω → ℝ` at quantile level `η` (Kouvelis–Xiao–Yang, p. 7, the formula used in (1)–(2)):
`CVaR_η(X) = max_{v ∈ ℝ} { v + (1/η) E[min{X − v, 0}] }`.
It is the real supremum over `v ∈ ℝ`; when `X` is `μ`-integrable and `0 < η ≤ 1` the bracket is
bounded above by `E[X]`, so the supremum is genuine. For a non-integrable `X` the Bochner
integral is `0` and the value is junk; every statement using `cvar` on a general `X` assumes
integrability. -/
noncomputable def cvar {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (η : ℝ)
    (X : Ω → ℝ) : ℝ :=
  ⨆ v : ℝ, v + (1 / η) * ∫ ω, min (X ω - v) 0 ∂μ

end RiskPostpone.Threshold


