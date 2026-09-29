-- Prove2me | Definitions.Def_FoundationsML_Ranking_RankBoostWeightedEps
-- name    : FoundationsML_Ranking_RankBoostWeightedEps
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:39:47.598325+00:00
-- url     : https://prove2.me/theorems/bdd1a3d9-92c3-4686-9637-670906d4398c
-- title:
--   RankBoost's weighted pairwise-outcome fraction ε^s (Eq. 10.11)
-- statement:
--   **Eq. (10.11), p. 244, PDF p. 261.** $\epsilon^s = \sum_{i=1}^m D(i)
--   \mathbb 1_{y_i(h(x'_i)-h(x_i))=s}$, for $s\in\{-1,0,+1\}$ and a distribution $D$ over
--   sample indices.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Eq. (10.11), p. 244 (PDF p. 261)

import Mathlib

namespace FoundationsML.Ranking

/-- RankBoost's weighted fraction of pairs with a given pairwise outcome `s ∈ {−1,0,+1}` for a
base ranker `h : X → ℝ` under a distribution `D : Fin m → ℝ` over pairwise-labeled sample
indices (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT
Press 2018, Eq. (10.11), p. 244, PDF p. 261): `ε^s = ∑_{i=1}^m D(i) 1_{y_i(h(x'_i)−h(x_i))=s}`.
`RankBoostEpsilonPlus`/`RankBoostEpsilonMinus` are this at `s = 1`/`s = -1`. -/
noncomputable def RankBoostWeightedEps {X : Type*} {m : ℕ}
    (D : Fin m → ℝ) (S1 S2 : Fin m → X) (y : Fin m → ℝ) (h : X → ℝ) (s : ℝ) : ℝ :=
  ∑ i, D i * (if y i * (h (S2 i) - h (S1 i)) = s then (1 : ℝ) else 0)

end FoundationsML.Ranking


