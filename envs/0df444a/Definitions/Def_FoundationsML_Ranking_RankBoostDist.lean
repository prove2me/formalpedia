-- Prove2me | Definitions.Def_FoundationsML_Ranking_RankBoostDist
-- name    : FoundationsML_Ranking_RankBoostDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:41:15.957915+00:00
-- url     : https://prove2.me/theorems/e76512e7-cf11-46aa-a54b-5c51b3d95111
-- title:
--   RankBoost's round-t distribution D_t
-- statement:
--   **Figure 10.1, p. 245, PDF p. 262.** `D_1` uniform; `D_{t+1}` from `D_t` by the
--   exponential-weight update using the `t`-th selected base ranker `h t` and RankBoost's own
--   `α_t`, normalized by `Z_t`.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Figure 10.1, p. 245 (PDF p. 262)

import Mathlib
import Definitions.Def_FoundationsML_Ranking_RankBoostWeightedEps
import Definitions.Def_FoundationsML_Ranking_RankBoostAlpha
import Definitions.Def_FoundationsML_Ranking_RankBoostNormalizer

namespace FoundationsML.Ranking

/-- RankBoost's sample-weight distribution `D_t` at the start of round `t` (`t = 0` is the
initial uniform distribution `D_1` of Figure 10.1 lines 1-2; `t + 1` is `D_{t+2}`, obtained
from `D_{t+1}` by the update of Figure 10.1 line 8, using the `t`-th selected base ranker
`h t`) (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press
2018, Figure 10.1, p. 245, PDF p. 262). -/
noncomputable def RankBoostDist {X : Type*} {m : ℕ}
    (S1 S2 : Fin m → X) (y : Fin m → ℝ) (h : ℕ → X → ℝ) : ℕ → Fin m → ℝ
  | 0 => fun _ => 1 / (m : ℝ)
  | t + 1 => fun i =>
      let D := RankBoostDist S1 S2 y h t
      let εPlus := RankBoostWeightedEps D S1 S2 y (h t) 1
      let εMinus := RankBoostWeightedEps D S1 S2 y (h t) (-1)
      let ε0 := RankBoostWeightedEps D S1 S2 y (h t) 0
      let α := RankBoostAlpha εPlus εMinus
      D i * Real.exp (-α * y i * (h t (S2 i) - h t (S1 i))) /
        RankBoostNormalizer εPlus εMinus ε0

end FoundationsML.Ranking


