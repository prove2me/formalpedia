-- Prove2me | Definitions.Def_AnalystRanking_Revelation_fcastJoint
-- name    : AnalystRanking_Revelation_fcastJoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:35:44.751084+00:00
-- url     : https://prove2.me/theorems/a3c83ef5-181b-42b0-83d4-de5b0bd232c5
-- title:
--   Joint forecast law $\Pr(m_i,m_j\mid\omega)$
-- statement:
--   When both analysts play $\sigma$, the forecast pair $(m_i,m_j)$ has, given the state $\omega$, the law
--   $$\Pr(m_i,m_j\mid\omega)=\sum_{s,t\in\{h,l\}}\Pr(s,t\mid\omega)\Pr_\sigma(m_i\mid s)\Pr_\sigma(m_j\mid t).$$
--   It is the input of forecast informativeness (§5, p. 24; (B.45), p. 53).
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §5, Definition 3, p. 24; (B.45), p. 53

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_sigProb
import Definitions.Def_AnalystRanking_Revelation_fprob

namespace AnalystRanking.Revelation

/-- **Joint law of the two forecasts given the state.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §5, p. 24 (`Π` is computed from the forecasts `(m_i, m_j)` under the symmetric strategy `σ`),
and the expansion (B.45), p. 53: `Pr(m_i, m_j | ω) = Σ_{s, t} Pr(s, t | ω) Pr_σ(m_i | s) Pr_σ(m_j | t)`.

**Formalization Note.** The signal law is (1)–(2) per ordered pair (see `sigProb`). -/
noncomputable def fcastJoint (γ ρ : ℝ) (σ : ℝ × ℝ) (ω mi mj : Bool) : ℝ :=
  ∑ s : Bool, ∑ t : Bool, sigProb γ ρ ω s t * fprob σ s mi * fprob σ t mj

end AnalystRanking.Revelation


