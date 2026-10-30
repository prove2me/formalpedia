-- Prove2me | Definitions.Def_AnalystRanking_Revelation_sigProb
-- name    : AnalystRanking_Revelation_sigProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:31:00.191498+00:00
-- url     : https://prove2.me/theorems/35137aaf-787c-47b1-b977-9d3418c09c4f
-- title:
--   Joint signal law $\Pr(s_i,s_j\mid\omega)$, (1)–(2)
-- statement:
--   Given the state $\omega$, the two analysts' signals $(s_i,s_j)$ have the joint law
--   $$\Pr(s_i,s_j\mid\omega)=\begin{cases}\Pr(s_i\mid\omega)\Pr(s_j\mid\omega)+\chi,& s_i=s_j,\\ \Pr(s_i\mid\omega)\Pr(s_j\mid\omega)-\chi,& s_i\neq s_j,\end{cases}\qquad \chi=\rho\gamma(1-\gamma),$$
--   where $\rho\in[0,1]$ is the conditional correlation ((1)–(2), p. 7). For example both signals are correct with probability $\rho\gamma+(1-\rho)\gamma^2$.
--
--   This law drives every belief an analyst forms about the other analyst's signal, and hence the ranking incentive.
--
--   **Formalization Note** The value is given for each *ordered* pair $(s_i,s_j)$. The display printed just before (1) gives $2(1-\rho)\gamma(1-\gamma)$ "if $s_i\neq s_j$", which is the probability of the event $s_i\neq s_j$; per ordered pair (1)–(2) give $(1-\rho)\gamma(1-\gamma)$, and only this makes the four probabilities sum to one.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §2, displays (1)–(2) and the display before (1), p. 7

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_sigMarg

namespace AnalystRanking.Revelation

/-- **Joint law of the two analysts' signals given the state, (1)–(2).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §2, displays (1)–(2), p. 7:
`Pr(s_i, s_j | ω) = Pr(s_i|ω) Pr(s_j|ω) + Cov(s_i, s_j|ω)` if `s_i = s_j`, and
`Pr(s_i|ω) Pr(s_j|ω) − Cov(s_i, s_j|ω)` if `s_i ≠ s_j`, where
`Cov(s_i, s_j|ω) = ρ γ (1 − γ) ≡ χ` and `ρ ∈ [0, 1]` is the conditional signal correlation.

`sigProb γ ρ ω s t` is `Pr(s_i = s, s_j = t | ω)` for the ordered pair `(s, t)`.

**Formalization Note.** Reading: the display printed just before (1) gives
`2(1 − ρ)γ(1 − γ)` "if `s_i ≠ s_j`", which is the probability of the *event* `s_i ≠ s_j`; per
ordered pair (1)–(2) give `(1 − ρ)γ(1 − γ)`, and only this makes the four probabilities sum to
`1`. The first two cases of that display, `ργ + (1 − ρ)γ²` and `ρ(1 − γ) + (1 − ρ)(1 − γ)²`, agree
with (1)–(2). -/
noncomputable def sigProb (γ ρ : ℝ) (ω s t : Bool) : ℝ :=
  sigMarg γ ω s * sigMarg γ ω t + (if s = t then ρ * γ * (1 - γ) else -(ρ * γ * (1 - γ)))

end AnalystRanking.Revelation


