-- Prove2me | Definitions.Def_FoundationsML_Boosting_AdaBoostDist
-- name    : FoundationsML_Boosting_AdaBoostDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:04:14.07236+00:00
-- url     : https://prove2.me/theorems/55970adf-c5b7-46ab-8869-168d8b2994ff
-- title:
--   AdaBoost's sample-weight distribution D_t (Figure 7.1)
-- statement:
--   **Figure 7.1, p. 146, PDF p. 163.** AdaBoost maintains a distribution $D_t$ over the sample
--   indices $\{1,\dots,m\}$: $D_1(i)=1/m$ for all $i$ (lines 1-2), and, at each round $t$, after
--   selecting $h_t$ with weighted error $\varepsilon_t$ and setting $\alpha_t$, $Z_t$
--   accordingly, $D_{t+1}(i) = D_t(i)\exp(-\alpha_t y_i h_t(x_i))/Z_t$ (line 8).
--
--   **Formalization Note.** `AdaBoostDist S y h : ℕ → Fin m → ℝ` indexes rounds from `0`
--   (`AdaBoostDist ... 0` is the book's $D_1$) so that `AdaBoostDist ... t` is the book's $D_{t+1}$;
--   `h : ℕ → X → ℝ` supplies the base classifier actually selected at each round (the output of
--   the weak learner / the $\arg\min$ of Figure 7.1 line 4, taken as external data, since only
--   the resulting weighted error $\varepsilon_t$, not the $\arg\min$ property itself, is used by
--   Theorems 7.2 and 7.7).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 146, Figure 7.1 (PDF p. 163)

import Mathlib
import Definitions.Def_FoundationsML_Boosting_WeightedError
import Definitions.Def_FoundationsML_Boosting_AdaBoostAlpha
import Definitions.Def_FoundationsML_Boosting_AdaBoostNormalizer

namespace FoundationsML.Boosting

/-- AdaBoost's sample-weight distribution `D_t` at the start of round `t` (`t = 0` is the
initial uniform distribution `D_1` of Figure 7.1 lines 1-2; `t + 1` is `D_{t+2}`, obtained from
`D_{t+1}` by the update of Figure 7.1 line 8, using the `t`-th selected base classifier `h t`)
(Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018,
Figure 7.1, p. 146, PDF p. 163). -/
noncomputable def AdaBoostDist {X : Type*} {m : ℕ}
    (S : Fin m → X) (y : Fin m → ℝ) (h : ℕ → X → ℝ) : ℕ → Fin m → ℝ
  | 0 => fun _ => 1 / (m : ℝ)
  | t + 1 => fun i =>
      let D := AdaBoostDist S y h t
      let ε := WeightedError D S y (h t)
      let α := AdaBoostAlpha ε
      D i * Real.exp (-α * y i * h t (S i)) / AdaBoostNormalizer ε

end FoundationsML.Boosting


