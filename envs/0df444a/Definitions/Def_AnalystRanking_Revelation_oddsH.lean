-- Prove2me | Definitions.Def_AnalystRanking_Revelation_oddsH
-- name    : AnalystRanking_Revelation_oddsH
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:38:18.368228+00:00
-- url     : https://prove2.me/theorems/ca7e61de-1646-47b1-9014-7daa0b3abb24
-- title:
--   Posterior odds after a high signal
-- statement:
--   $$\frac{\Pr(H\mid h)}{\Pr(L\mid h)}=\frac{q\gamma}{(1-q)(1-\gamma)},$$ by Bayes' rule (the ratio in (A.8a), p. 32).
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Appendix A, (A.8a), p. 32

import Mathlib

namespace AnalystRanking.Revelation

/-- **Posterior odds after a high signal, `Pr(H|h)/Pr(L|h)`.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Appendix A, (A.8a), p. 32: by Bayes' rule `Pr(H|h)/Pr(L|h) = qγ/((1 − q)(1 − γ))`.

**Formalization Note.** Statements assume `0 < q < 1`, `0 < γ < 1`. -/
noncomputable def oddsH (q γ : ℝ) : ℝ :=
  q * γ / ((1 - q) * (1 - γ))

end AnalystRanking.Revelation


