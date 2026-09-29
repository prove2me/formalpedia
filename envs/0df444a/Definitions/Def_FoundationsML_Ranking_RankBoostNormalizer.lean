-- Prove2me | Definitions.Def_FoundationsML_Ranking_RankBoostNormalizer
-- name    : FoundationsML_Ranking_RankBoostNormalizer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:40:33.043299+00:00
-- url     : https://prove2.me/theorems/4391c38e-3187-4dc2-b553-2a44c3ad2ac2
-- title:
--   RankBoost's per-round normalization factor Z_t
-- statement:
--   **Figure 10.1 line 6, p. 245, PDF p. 262.** $Z(\epsilon^+,\epsilon^-,\epsilon^0) =
--   \epsilon^0 + 2\sqrt{\epsilon^+\epsilon^-}$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Figure 10.1 line 6, p. 245 (PDF p. 262)

import Mathlib

namespace FoundationsML.Ranking

/-- RankBoost's per-round normalization factor `Z_t`, as a function of the base ranker's
weighted pairwise-outcome fractions `ε^+`, `ε^-`, `ε^0` (Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Figure 10.1 line 6, p. 245, PDF p.
262): `Z(ε^+,ε^-,ε^0) = ε^0 + 2·sqrt(ε^+ ε^-)`. -/
noncomputable def RankBoostNormalizer (εPlus εMinus ε0 : ℝ) : ℝ :=
  ε0 + 2 * Real.sqrt (εPlus * εMinus)

end FoundationsML.Ranking


