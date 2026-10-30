-- Prove2me | Definitions.Def_AnalystRanking_Revelation_sigProbMarg
-- name    : AnalystRanking_Revelation_sigProbMarg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:32:38.013699+00:00
-- url     : https://prove2.me/theorems/bdc5b953-59e6-4a80-ad31-c915193de831
-- title:
--   Signal probability $\Pr(s)$
-- statement:
--   The unconditional probability of the signal $s$ is
--   $$\Pr(s)=\sum_{\omega\in\{H,L\}}\Pr(\omega)\Pr(s\mid\omega),$$
--   so $\Pr(h)=q\gamma+(1-q)(1-\gamma)$ and $\Pr(l)=q(1-\gamma)+(1-q)\gamma$. It normalizes the Bayes beliefs $\Pr(\omega\mid s)$ required by Definition 1 (ii), p. 9.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §2, p. 6; Definition 1 (ii), p. 9

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_prior
import Definitions.Def_AnalystRanking_Revelation_sigMarg

namespace AnalystRanking.Revelation

/-- **Unconditional probability of a signal, `Pr(s)`.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §2, p. 6 (prior `q` and precision `γ`): `Pr(s) = Σ_ω Pr(ω) Pr(s | ω)`, so
`Pr(h) = qγ + (1 − q)(1 − γ)` and `Pr(l) = q(1 − γ) + (1 − q)γ`. It is the normalizing constant
of the Bayes beliefs `Pr(ω | s)` of Definition 1 (ii), p. 9.

**Formalization Note.** For `0 < q < 1` and `0 < γ < 1` it is positive. -/
noncomputable def sigProbMarg (q γ : ℝ) (s : Bool) : ℝ :=
  ∑ ω : Bool, prior q ω * sigMarg γ ω s

end AnalystRanking.Revelation


