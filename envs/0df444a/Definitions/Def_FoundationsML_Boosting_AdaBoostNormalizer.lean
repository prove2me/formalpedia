-- Prove2me | Definitions.Def_FoundationsML_Boosting_AdaBoostNormalizer
-- name    : FoundationsML_Boosting_AdaBoostNormalizer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:03:40.800829+00:00
-- url     : https://prove2.me/theorems/1bf10a2c-9c85-4edb-baa0-6f31b7b769c3
-- title:
--   AdaBoost's per-round normalization factor (Figure 7.1, line 6)
-- statement:
--   **Figure 7.1, line 6, p. 146, PDF p. 163.** Given the weighted error $\varepsilon$ of the
--   round's selected base classifier, AdaBoost's normalization factor is
--   $Z=2\sqrt{\varepsilon(1-\varepsilon)}$ (the closed form the book's own pseudocode displays,
--   later re-derived from the raw normalizing-sum definition in the proof of Theorem 7.2).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 146, Figure 7.1 line 6 (PDF p. 163)

import Mathlib

namespace FoundationsML.Boosting

/-- AdaBoost's per-round normalization factor `Z_t`, as a function of the base classifier's
weighted error `ε` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd
ed., MIT Press 2018, Figure 7.1 line 6, p. 146, PDF p. 163): `Z(ε) = 2·sqrt(ε(1−ε))`. -/
noncomputable def AdaBoostNormalizer (ε : ℝ) : ℝ := 2 * Real.sqrt (ε * (1 - ε))

end FoundationsML.Boosting


