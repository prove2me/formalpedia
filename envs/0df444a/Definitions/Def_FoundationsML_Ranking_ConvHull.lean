-- Prove2me | Definitions.Def_FoundationsML_Ranking_ConvHull
-- name    : FoundationsML_Ranking_ConvHull
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:39:27.824052+00:00
-- url     : https://prove2.me/theorems/024a8215-50a6-4980-827e-8cd587e61ffa
-- title:
--   Convex hull of a hypothesis set
-- statement:
--   **Referenced p. 250, PDF p. 267.** $\mathrm{conv}(H)$, the set of finite convex
--   combinations of elements of $H$. Restated locally since a draft cannot import chunk
--   `07-boosting`'s own copy.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, referenced p. 250 (PDF p. 267)

import Mathlib

namespace FoundationsML.Ranking

/-- The convex hull `conv(H)` of a family `H` of real-valued functions on `X` (Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, referenced
at p. 250, PDF p. 267, restated locally for this chapter since drafts cannot import chunk
`07-boosting`'s own draft copy): the set of finite convex combinations of elements of `H`. -/
def ConvHull {X : Type*} (H : Set (X → ℝ)) : Set (X → ℝ) :=
  {g | ∃ (n : ℕ) (c : Fin n → ℝ) (h : Fin n → (X → ℝ)),
    (∀ i, h i ∈ H) ∧ (∀ i, 0 ≤ c i) ∧ (∑ i, c i = 1) ∧ g = fun x => ∑ i, c i * h i x}

end FoundationsML.Ranking


