-- Prove2me | Definitions.Def_FoundationsML_Boosting_AdaBoostAlpha
-- name    : FoundationsML_Boosting_AdaBoostAlpha
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:03:14.604985+00:00
-- url     : https://prove2.me/theorems/1666d572-5424-4f1a-b165-b38120e54e88
-- title:
--   AdaBoost's per-round coefficient (Figure 7.1, line 5)
-- statement:
--   **Figure 7.1, line 5, p. 146, PDF p. 163.** Given the weighted error $\varepsilon$ of the
--   round's selected base classifier, AdaBoost sets $\alpha=\frac12\log\frac{1-\varepsilon}
--   \varepsilon$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 146, Figure 7.1 line 5 (PDF p. 163)

import Mathlib

namespace FoundationsML.Boosting

/-- AdaBoost's per-round coefficient `α_t`, as a function of the base classifier's weighted
error `ε` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT
Press 2018, Figure 7.1 line 5, p. 146, PDF p. 163): `α(ε) = (1/2)·log((1−ε)/ε)`. -/
noncomputable def AdaBoostAlpha (ε : ℝ) : ℝ := (1 / 2) * Real.log ((1 - ε) / ε)

end FoundationsML.Boosting


