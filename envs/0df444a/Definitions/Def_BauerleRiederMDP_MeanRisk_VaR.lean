-- Prove2me | Definitions.Def_BauerleRiederMDP_MeanRisk_VaR
-- name    : BauerleRiederMDP_MeanRisk_VaR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:26:43.604188+00:00
-- url     : https://prove2.me/theorems/25ac7eb5-c1e3-4680-ab16-c25725fae985
-- title:
--   Value-at-Risk $\mathrm{VaR}_\gamma(X)$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and let $X$ be a random variable, interpreted as a risk: positive values are rewards and negative values are losses. The **Value-at-Risk** of $X$ at level $\gamma\in(0,1)$ is
--
--   $$
--   \mathrm{VaR}_\gamma(X):=\inf\{x\in\mathbb R \mid \mathbb P(x+X<0)\le 1-\gamma\},
--   $$
--
--   the smallest amount of money which, added to $X$, makes the probability of a loss at most $1-\gamma$. It is the smallest $\gamma$-quantile of $-X$.
--
--   It is the building block of the Average-Value-at-Risk, the risk measure of the mean-risk problem of §4.7.
--
--   **Formalization Note** The probability is the real-valued measure of the event. For a probability measure and $\gamma\in(0,1)$ the set is nonempty and bounded below, so the infimum is a real number.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Example C.2.2 a), p.368 (PDF p.373); sign convention §C.2, p.367 (PDF p.372)

import Mathlib

open MeasureTheory

namespace BauerleRiederMDP.MeanRisk

/-- The Value-at-Risk of a risk `X` at level `γ`, Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), Example C.2.2 a), p.368 (PDF 373):
`VaR_γ(X) := inf {x ∈ ℝ | ℙ(x + X < 0) ≤ 1 − γ}`.
Positive values of `X` are rewards and negative values are losses (§C.2, p.367).

**Formalization Note.** `P` is the probability measure `ℙ`; the probability is the real-valued
`P.real`. For a probability measure and `γ ∈ (0,1)` the set is nonempty and bounded below, so the
real `sInf` is the book's infimum; the definition is only used for such `γ`. -/
noncomputable def VaR {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (X : Ω → ℝ) : ℝ :=
  sInf {x : ℝ | P.real {ω | x + X ω < 0} ≤ 1 - γ}

end BauerleRiederMDP.MeanRisk


