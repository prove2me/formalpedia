-- Prove2me | Definitions.Def_AnalystRanking_Revelation_prior
-- name    : AnalystRanking_Revelation_prior
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:30:06.065993+00:00
-- url     : https://prove2.me/theorems/7fa7a59e-74a3-47ca-8f41-19c37d51bd8c
-- title:
--   Prior on the state, $\Pr(H)=q$
-- statement:
--   Two risk-neutral analysts forecast a binary state $\omega\in\{H,L\}$ with prior $\Pr(H)=q\in(0,1)$. Each receives a private signal $s\in\{h,l\}$ of precision $\gamma=\Pr(s=\omega\mid\omega)\in(\tfrac12,1)$; conditional on the state the two signals have correlation $\rho\in[0,1]$, and $\chi=\rho\gamma(1-\gamma)$ is their conditional covariance.
--
--   For $q\in\mathbb R$ and $\omega\in\{H,L\}$ define
--   $$\Pr(\omega)=\begin{cases}q,&\omega=H,\\ 1-q,&\omega=L.\end{cases}$$
--
--   This is the prior of §2 (p. 6); every expected payoff and every posterior in the model is computed from it.
--
--   **Formalization Note** The state set $\{H,L\}$ is encoded as `Bool` with `true` $=H$. Statements assume $0<q<1$.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §2, p. 6

import Mathlib

namespace AnalystRanking.Revelation

/-- **Prior on the state, `Pr(ω)`.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §2, p. 6: "The state can be high or low, `ω ∈ {H, L}`, with a prior distribution
`Pr(H) = q ∈ (0, 1)`."

`prior q ω` is `Pr(ω)`, with `true = H` and `false = L`.

**Formalization Note.** The state set `{H, L}` is encoded as `Bool` (`true = H`). Statements
using `prior` assume `0 < q < 1`. -/
noncomputable def prior (q : ℝ) (ω : Bool) : ℝ :=
  if ω then q else 1 - q

end AnalystRanking.Revelation


