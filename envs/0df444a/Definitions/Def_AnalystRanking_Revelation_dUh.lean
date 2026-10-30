-- Prove2me | Definitions.Def_AnalystRanking_Revelation_dUh
-- name    : AnalystRanking_Revelation_dUh
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:39:16.462023+00:00
-- url     : https://prove2.me/theorems/bf2ffefb-68a7-41e0-9cac-d27c9c50ade3
-- title:
--   Net payoff of a truthful high forecast, $\Delta U^h_i$
-- statement:
--   When the other analyst plays $\sigma=(\sigma^h,\sigma^l)$, a high-signal analyst's net expected payoff from forecasting high rather than low is
--   $$\Delta U^h_i(\sigma^h,\sigma^l,q)=U_i(\hat h\mid h)-U_i(\hat l\mid h)$$
--   ((A.1), p. 30; (A.5), p. 31), computed from the model's primitives.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Appendix A, (A.1), p. 30, (A.5), p. 31

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_interimPay

namespace AnalystRanking.Revelation

/-- **Net payoff of a truthful high forecast, `ΔUʰ_i`, (A.1), (A.5).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Appendix A, (A.1), p. 30, and (A.5), p. 31:
`ΔUʰ_i ≡ U_i(ĥ | h) − U_i(l̂ | h)`, when the other analyst plays `σ` (written `ΔUʰ_i(σʰ, σˡ, q)`).

**Formalization Note.** Built from `interimPay` (the primitives (1)–(3) with Bayes beliefs). -/
noncomputable def dUh (w1 w0 w2 q γ ρ : ℝ) (σ : ℝ × ℝ) : ℝ :=
  interimPay w1 w0 w2 q γ ρ σ true true - interimPay w1 w0 w2 q γ ρ σ true false

end AnalystRanking.Revelation


