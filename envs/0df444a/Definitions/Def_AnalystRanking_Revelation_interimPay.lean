-- Prove2me | Definitions.Def_AnalystRanking_Revelation_interimPay
-- name    : AnalystRanking_Revelation_interimPay
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:33:17.424294+00:00
-- url     : https://prove2.me/theorems/b36d334a-c736-4d0c-b2d9-ce545c35206a
-- title:
--   Interim expected rank payoff $U_i(m\mid s)$, (A.1)
-- statement:
--   Two risk-neutral analysts forecast a binary state $\omega\in\{H,L\}$ with prior $\Pr(H)=q\in(0,1)$. Each receives a private signal $s\in\{h,l\}$ of precision $\gamma=\Pr(s=\omega\mid\omega)\in(\tfrac12,1)$; conditional on the state the two signals have correlation $\rho\in[0,1]$, and $\chi=\rho\gamma(1-\gamma)$ is their conditional covariance. Payoffs are those of (3), and the other analyst forecasts according to the strategy $\sigma$.
--
--   The interim expected payoff of forecasting $m$ after observing $s$ is
--   $$U_i(m\mid s)=\mathbb E_{\omega,m_j}\big[u_i(m,m_j,\omega)\mid s\big]=\frac{1}{\Pr(s)}\sum_{\omega}\sum_{t}\sum_{m_j}\Pr(\omega)\Pr(s,t\mid\omega)\Pr_\sigma(m_j\mid t)\,u_i(m,m_j,\omega),$$
--   with Bayes beliefs as in Definition 1 (p. 9) and (A.1) (p. 30).
--
--   This is the objective an analyst maximizes in equilibrium; its differences $\Delta U^h_i$, $\Delta U^l_i$ drive every result.
--
--   **Formalization Note** The joint signal law is (1)–(2) per ordered pair.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Definition 1, display (5), p. 9; Appendix A, (A.1), p. 30

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_prior
import Definitions.Def_AnalystRanking_Revelation_sigProb
import Definitions.Def_AnalystRanking_Revelation_fprob
import Definitions.Def_AnalystRanking_Revelation_rankPay
import Definitions.Def_AnalystRanking_Revelation_sigProbMarg

namespace AnalystRanking.Revelation

/-- **Interim expected rank payoff `U_i(m | s)`, (A.1) and (5).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Definition 1 (i)–(ii), display (5), p. 9, and Appendix A, (A.1), p. 30:
`U_i(m_i | s_i) ≡ 𝔼_{ω, m_j}[u_i(m_i, m_j, ω) | s_i]`, with beliefs `Pr(ω | s_i)` and
`Pr(s_j | s_i)` given by Bayes' rule and the other analyst playing the strategy `σ`.

`interimPay w1 w0 w2 q γ ρ σ s m` is
`Σ_{ω, t, m_j} Pr(ω) Pr(s, t | ω) Pr_σ(m_j | t) u(m, m_j, ω) / Pr(s)`.

**Formalization Note.** Payoffs are the triple `(w₁, w₀, w₂)` of (3); the signal law is (1)–(2)
per ordered pair (see `sigProb`); `Bool` encodes `{h, l}`, `{ĥ, l̂}`, `{H, L}` (`true` = high).
The division by `Pr(s) > 0` is Bayes' rule. -/
noncomputable def interimPay (w1 w0 w2 q γ ρ : ℝ) (σ : ℝ × ℝ) (s m : Bool) : ℝ :=
  (∑ ω : Bool, ∑ t : Bool, ∑ mj : Bool,
      prior q ω * sigProb γ ρ ω s t * fprob σ t mj * rankPay w1 w0 w2 m mj ω) /
    sigProbMarg q γ s

end AnalystRanking.Revelation


