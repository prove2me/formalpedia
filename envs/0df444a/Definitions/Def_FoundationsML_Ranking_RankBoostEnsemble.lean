-- Prove2me | Definitions.Def_FoundationsML_Ranking_RankBoostEnsemble
-- name    : FoundationsML_Ranking_RankBoostEnsemble
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:43:21.040577+00:00
-- url     : https://prove2.me/theorems/564e0dcb-f696-4b9b-af81-503129bc4f5f
-- title:
--   RankBoost's returned function f (Figure 10.1 lines 9-10)
-- statement:
--   **Figure 10.1 lines 9-10, p. 245, PDF p. 262.** $f = \sum_{t=1}^T \alpha_t h_t$, with
--   `α_t`/`ε_t^+`/`ε_t^-` RankBoost's own.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Figure 10.1 lines 9-10, p. 245 (PDF p. 262)

import Mathlib
import Definitions.Def_FoundationsML_Ranking_RankBoostAlpha
import Definitions.Def_FoundationsML_Ranking_RankBoostEpsilonPlus
import Definitions.Def_FoundationsML_Ranking_RankBoostEpsilonMinus

namespace FoundationsML.Ranking

/-- The function `f = ∑_{t=1}^T α_t h_t` returned by RankBoost after `T` rounds of boosting
(Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018,
Figure 10.1 lines 9-10, p. 245, PDF p. 262), with `α_t = RankBoostAlpha ε_t^+ ε_t^-` and
`ε_t^+`, `ε_t^-` RankBoost's own round-`t` weighted pairwise-outcome fractions. -/
noncomputable def RankBoostEnsemble {X : Type*} {m : ℕ}
    (S1 S2 : Fin m → X) (y : Fin m → ℝ) (h : ℕ → X → ℝ) (T : ℕ) : X → ℝ :=
  fun x => ∑ t ∈ Finset.range T,
    RankBoostAlpha (RankBoostEpsilonPlus S1 S2 y h t) (RankBoostEpsilonMinus S1 S2 y h t) * h t x

end FoundationsML.Ranking


