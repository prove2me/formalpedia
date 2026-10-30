-- Prove2me | Definitions.Def_AnalystRanking_Revelation_oddsL
-- name    : AnalystRanking_Revelation_oddsL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:38:34.406113+00:00
-- url     : https://prove2.me/theorems/a5f3a8b4-94cc-4213-a603-5548f7b9a493
-- title:
--   Posterior odds after a low signal
-- statement:
--   $$\frac{\Pr(H\mid l)}{\Pr(L\mid l)}=\frac{q(1-\gamma)}{(1-q)\gamma},$$ by Bayes' rule (the ratio in (A.8b), p. 32).
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Appendix A, (A.8b), p. 32

import Mathlib

namespace AnalystRanking.Revelation

/-- **Posterior odds after a low signal, `Pr(H|l)/Pr(L|l)`.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Appendix A, (A.8b), p. 32: by Bayes' rule `Pr(H|l)/Pr(L|l) = q(1 − γ)/((1 − q)γ)`.

**Formalization Note.** Statements assume `0 < q < 1`, `0 < γ < 1`. -/
noncomputable def oddsL (q γ : ℝ) : ℝ :=
  q * (1 - γ) / ((1 - q) * γ)

end AnalystRanking.Revelation


