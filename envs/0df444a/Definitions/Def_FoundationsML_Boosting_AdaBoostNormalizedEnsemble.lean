-- Prove2me | Definitions.Def_FoundationsML_Boosting_AdaBoostNormalizedEnsemble
-- name    : FoundationsML_Boosting_AdaBoostNormalizedEnsemble
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:06:43.086498+00:00
-- url     : https://prove2.me/theorems/4e5a6557-52ae-446b-a1b0-a96b6978aba8
-- title:
--   The normalized ensemble f-bar (p. 156)
-- statement:
--   **p. 156, PDF p. 173.** The normalized version of the function returned by AdaBoost is
--   $\bar f = f/\sum_{t=1}^T\alpha_t = f/\|\alpha\|_1$, used in Theorem 7.7's margin bound
--   (whereas Theorem 7.2's empirical-error bound uses the raw $f$).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 156 (PDF p. 173)

import Mathlib
import Definitions.Def_FoundationsML_Boosting_AdaBoostAlpha
import Definitions.Def_FoundationsML_Boosting_AdaBoostEpsilon
import Definitions.Def_FoundationsML_Boosting_AdaBoostEnsemble

namespace FoundationsML.Boosting

/-- The normalized combination `f̄ = f / ∑_{t=1}^T α_t` of the function returned by AdaBoost
after `T` rounds of boosting (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, p. 156, PDF p. 173), used in Theorem 7.7's margin bound.
Since the `α_t` are the outputs of AdaBoost's own weighted-error-based rule, this is `f`
rescaled by the (nonnegative) `L¹` norm of its coefficient vector `α`. -/
noncomputable def AdaBoostNormalizedEnsemble {X : Type*} {m : ℕ}
    (S : Fin m → X) (y : Fin m → ℝ) (h : ℕ → X → ℝ) (T : ℕ) : X → ℝ :=
  fun x => AdaBoostEnsemble S y h T x /
    ∑ t ∈ Finset.range T, AdaBoostAlpha (AdaBoostEpsilon S y h t)

end FoundationsML.Boosting


