-- Prove2me | Definitions.Def_AnalystRanking_Revelation_dUl
-- name    : AnalystRanking_Revelation_dUl
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:39:57.180211+00:00
-- url     : https://prove2.me/theorems/b92f5a15-e8c7-48d0-be46-a49378362b85
-- title:
--   Net payoff of a truthful low forecast, $\Delta U^l_i$
-- statement:
--   When the other analyst plays $\sigma=(\sigma^h,\sigma^l)$, a low-signal analyst's net expected payoff from forecasting low rather than high is
--   $$\Delta U^l_i(\sigma^h,\sigma^l,q)=U_i(\hat l\mid l)-U_i(\hat h\mid l)$$
--   ((A.1), p. 30; (A.2), p. 31), computed from the model's primitives.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Appendix A, (A.1), p. 30, (A.2), p. 31

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_interimPay

namespace AnalystRanking.Revelation

/-- **Net payoff of a truthful low forecast, `ΔUˡ_i`, (A.1), (A.2).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Appendix A, (A.1), p. 30, and (A.2), p. 31:
`ΔUˡ_i ≡ U_i(l̂ | l) − U_i(ĥ | l)`, when the other analyst plays `σ` (written `ΔUˡ_i(σʰ, σˡ, q)`).

**Formalization Note.** Built from `interimPay` (the primitives (1)–(3) with Bayes beliefs). -/
noncomputable def dUl (w1 w0 w2 q γ ρ : ℝ) (σ : ℝ × ℝ) : ℝ :=
  interimPay w1 w0 w2 q γ ρ σ false false - interimPay w1 w0 w2 q γ ρ σ false true

end AnalystRanking.Revelation


