-- Prove2me | Definitions.Def_FoundationsML_Boosting_AdaBoostEpsilon
-- name    : FoundationsML_Boosting_AdaBoostEpsilon
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:04:50.99362+00:00
-- url     : https://prove2.me/theorems/ef9bd209-98e0-4142-8532-4b1446b9c2dc
-- title:
--   AdaBoost's own round-t weighted error (epsilon_t)
-- statement:
--   **Figure 7.1, line 4, p. 146, PDF p. 163.** AdaBoost's round-$t$ weighted error is
--   $\varepsilon_t = \Pr_{i\sim D_t}[h_t(x_i)\ne y_i]$, the weighted error of AdaBoost's own
--   round-$t$ base classifier $h_t$ under AdaBoost's own round-$t$ distribution $D_t$ — not an
--   arbitrary error rate, but the one produced by AdaBoost's own recursion.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 146, Figure 7.1 line 4 (PDF p. 163)

import Mathlib
import Definitions.Def_FoundationsML_Boosting_WeightedError
import Definitions.Def_FoundationsML_Boosting_AdaBoostDist

namespace FoundationsML.Boosting

/-- AdaBoost's own round-`t` weighted error `ε_t`, the error of the `t`-th selected base
classifier `h t` under AdaBoost's own distribution `D_t` at that round (Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Figure 7.1 line 4, p.
146, PDF p. 163): `ε_t = P_{i∼D_t}[h_t(x_i) ≠ y_i]`. -/
noncomputable def AdaBoostEpsilon {X : Type*} {m : ℕ}
    (S : Fin m → X) (y : Fin m → ℝ) (h : ℕ → X → ℝ) (t : ℕ) : ℝ :=
  WeightedError (AdaBoostDist S y h t) S y (h t)

end FoundationsML.Boosting


