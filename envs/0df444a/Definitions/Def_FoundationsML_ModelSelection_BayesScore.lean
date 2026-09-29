-- Prove2me | Definitions.Def_FoundationsML_ModelSelection_BayesScore
-- name    : FoundationsML_ModelSelection_BayesScore
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:18:50.735622+00:00
-- url     : https://prove2.me/theorems/d425e38f-1842-4eae-95a8-6a5be97c6ae2
-- title:
--   Bayes scoring function (Eq. 4.9)
-- statement:
--   **Eq. (4.9), p. 74, PDF p. 91.** For a conditional label probability
--   $\eta(x) = \Pr[y=+1\mid x]$, the Bayes scoring function is $h^*(x) = \eta(x) - \frac12$; its
--   sign induces the Bayes classifier. Used by Theorem 4.7's excess-error bound.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Eq. (4.9), p. 74 (PDF p. 91)

import Mathlib

namespace FoundationsML.ModelSelection

/-- The Bayes scoring function for a real-valued scoring problem with conditional label
probability `η(x) = P[y = +1 | x]` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, Eq. (4.9), p. 74, PDF p. 91): `h*(x) = η(x) − 1/2`. -/
noncomputable def BayesScore {X : Type*} (η : X → ℝ) (x : X) : ℝ :=
  η x - 1 / 2

end FoundationsML.ModelSelection


