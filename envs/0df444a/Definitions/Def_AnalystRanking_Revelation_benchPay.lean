-- Prove2me | Definitions.Def_AnalystRanking_Revelation_benchPay
-- name    : AnalystRanking_Revelation_benchPay
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:33:57.599807+00:00
-- url     : https://prove2.me/theorems/421b46f2-8886-4b70-8e4e-6683aabb3695
-- title:
--   Interim expected benchmark payoff
-- statement:
--   In the benchmark (§3.1, p. 10) the analyst maximizes $\mathbb E_\omega[u_i(m,\omega)\mid s]$ with the accuracy payoff $W\mathbf 1[m=\omega]$:
--   $$U_i(m\mid s)=\frac{1}{\Pr(s)}\sum_{\omega}\Pr(\omega)\Pr(s\mid\omega)\,W\,\mathbf 1[m=\omega]=W\,\Pr(\omega=m\mid s),$$
--   identifying the forecast $\hat h$ with $H$ and $\hat l$ with $L$.
--   For instance $U_i(\hat l\mid l)=\Pr(L\mid l)W$. This payoff does not depend on the other analyst.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §3.1, p. 10

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_prior
import Definitions.Def_AnalystRanking_Revelation_sigMarg
import Definitions.Def_AnalystRanking_Revelation_accPay
import Definitions.Def_AnalystRanking_Revelation_sigProbMarg

namespace AnalystRanking.Revelation

/-- **Interim expected benchmark payoff `U_i(m | s)` without ranking.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), §3.1, p. 10: the analyst's objective is `max_σ 𝔼_ω[u_i(m_i(σ_i), ω) | s_i]`, e.g.
"`U_i(l̂ | l) = Pr(H|l) u_i(l̂, H) + Pr(L|l) u_i(l̂, L) = Pr(L|l) W`".

`benchPay W q γ s m` is `Σ_ω Pr(ω | s) u(m, ω) = Σ_ω Pr(ω) Pr(s | ω) u(m, ω) / Pr(s)`.

**Formalization Note.** `π_a = W`, `π_na = 0` (p. 10); `Bool` encodes the binary sets. -/
noncomputable def benchPay (W q γ : ℝ) (s m : Bool) : ℝ :=
  (∑ ω : Bool, prior q ω * sigMarg γ ω s * accPay W m ω) / sigProbMarg q γ s

end AnalystRanking.Revelation


