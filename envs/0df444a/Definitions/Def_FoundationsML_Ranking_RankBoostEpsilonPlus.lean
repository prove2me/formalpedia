-- Prove2me | Definitions.Def_FoundationsML_Ranking_RankBoostEpsilonPlus
-- name    : FoundationsML_Ranking_RankBoostEpsilonPlus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:42:06.915681+00:00
-- url     : https://prove2.me/theorems/953bb858-92cd-4494-8154-070313327be7
-- title:
--   RankBoost's own round-t ε_t^+
-- statement:
--   **Eq. (10.11), p. 244, PDF p. 261.** RankBoost's own `ε_t^+`, tied to its own `D_t` and
--   selected base ranker `h t` (not a free parameter), avoiding this chapter's trivialization
--   risk.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Eq. (10.11), p. 244 (PDF p. 261)

import Mathlib
import Definitions.Def_FoundationsML_Ranking_RankBoostWeightedEps
import Definitions.Def_FoundationsML_Ranking_RankBoostDist

namespace FoundationsML.Ranking

/-- RankBoost's own round-`t` weighted fraction `ε_t^+` of pairs correctly ranked by the
`t`-th selected base ranker `h t` under RankBoost's own distribution `D_t` at that round
(Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018,
Eq. (10.11), p. 244, PDF p. 261). -/
noncomputable def RankBoostEpsilonPlus {X : Type*} {m : ℕ}
    (S1 S2 : Fin m → X) (y : Fin m → ℝ) (h : ℕ → X → ℝ) (t : ℕ) : ℝ :=
  RankBoostWeightedEps (RankBoostDist S1 S2 y h t) S1 S2 y (h t) 1

end FoundationsML.Ranking


