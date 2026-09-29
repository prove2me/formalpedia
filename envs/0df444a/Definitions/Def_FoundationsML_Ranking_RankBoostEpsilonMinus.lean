-- Prove2me | Definitions.Def_FoundationsML_Ranking_RankBoostEpsilonMinus
-- name    : FoundationsML_Ranking_RankBoostEpsilonMinus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:42:45.38343+00:00
-- url     : https://prove2.me/theorems/86ec058b-5740-46ff-80a6-7c2c210dea8c
-- title:
--   RankBoost's own round-t ε_t^-
-- statement:
--   **Eq. (10.11), p. 244, PDF p. 261.** RankBoost's own `ε_t^-`, tied to its own `D_t` and
--   selected base ranker `h t`.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Eq. (10.11), p. 244 (PDF p. 261)

import Mathlib
import Definitions.Def_FoundationsML_Ranking_RankBoostWeightedEps
import Definitions.Def_FoundationsML_Ranking_RankBoostDist

namespace FoundationsML.Ranking

/-- RankBoost's own round-`t` weighted fraction `ε_t^-` of pairs misranked by the `t`-th
selected base ranker `h t` under RankBoost's own distribution `D_t` at that round (Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Eq.
(10.11), p. 244, PDF p. 261). -/
noncomputable def RankBoostEpsilonMinus {X : Type*} {m : ℕ}
    (S1 S2 : Fin m → X) (y : Fin m → ℝ) (h : ℕ → X → ℝ) (t : ℕ) : ℝ :=
  RankBoostWeightedEps (RankBoostDist S1 S2 y h t) S1 S2 y (h t) (-1)

end FoundationsML.Ranking


