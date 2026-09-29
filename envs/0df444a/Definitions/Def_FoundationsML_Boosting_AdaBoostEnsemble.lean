-- Prove2me | Definitions.Def_FoundationsML_Boosting_AdaBoostEnsemble
-- name    : FoundationsML_Boosting_AdaBoostEnsemble
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:06:08.548278+00:00
-- url     : https://prove2.me/theorems/f87a2afc-34e3-458d-bf6e-7dfd13db74cc
-- title:
--   The ensemble function f returned by AdaBoost (Figure 7.1)
-- statement:
--   **Figure 7.1, lines 9-10, p. 146, PDF p. 163.** After $T$ rounds of boosting, AdaBoost
--   returns $f=\sum_{t=1}^T\alpha_t h_t$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 146, Figure 7.1 lines 9-10 (PDF p. 163)

import Mathlib
import Definitions.Def_FoundationsML_Boosting_AdaBoostAlpha
import Definitions.Def_FoundationsML_Boosting_AdaBoostEpsilon

namespace FoundationsML.Boosting

/-- The function `f = ∑_{t=1}^T α_t h_t` returned by AdaBoost after `T` rounds of boosting
(Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018,
Figure 7.1 lines 9-10, p. 146, PDF p. 163), with `α_t = AdaBoostAlpha ε_t` and `ε_t` AdaBoost's
own round-`t` weighted error (`AdaBoostEpsilon`). -/
noncomputable def AdaBoostEnsemble {X : Type*} {m : ℕ}
    (S : Fin m → X) (y : Fin m → ℝ) (h : ℕ → X → ℝ) (T : ℕ) : X → ℝ :=
  fun x => ∑ t ∈ Finset.range T, AdaBoostAlpha (AdaBoostEpsilon S y h t) * h t x

end FoundationsML.Boosting


