-- Prove2me | Definitions.Def_FoundationsML_Ranking_RankBoostAlpha
-- name    : FoundationsML_Ranking_RankBoostAlpha
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:40:15.19306+00:00
-- url     : https://prove2.me/theorems/216f506f-b1f2-4c36-a4ce-41d5f0326e1d
-- title:
--   RankBoost's per-round coefficient α_t
-- statement:
--   **Figure 10.1 line 5, p. 245, PDF p. 262.** $\alpha(\epsilon^+,\epsilon^-) =
--   \frac12\log(\epsilon^+/\epsilon^-)$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Figure 10.1 line 5, p. 245 (PDF p. 262)

import Mathlib

namespace FoundationsML.Ranking

/-- RankBoost's per-round coefficient `α_t`, as a function of the base ranker's weighted
pairwise-outcome fractions `ε^+`, `ε^-` (Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, Figure 10.1 line 5, p. 245, PDF p. 262):
`α(ε^+,ε^-) = (1/2)·log(ε^+/ε^-)`. -/
noncomputable def RankBoostAlpha (εPlus εMinus : ℝ) : ℝ :=
  (1 / 2) * Real.log (εPlus / εMinus)

end FoundationsML.Ranking


