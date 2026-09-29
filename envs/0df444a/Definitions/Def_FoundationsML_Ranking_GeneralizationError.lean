-- Prove2me | Definitions.Def_FoundationsML_Ranking_GeneralizationError
-- name    : FoundationsML_Ranking_GeneralizationError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:35:53.809978+00:00
-- url     : https://prove2.me/theorems/a9daaf3f-eb5b-4a25-a0ca-7840fea1e5e4
-- title:
--   Generalization error (pairwise misranking risk)
-- statement:
--   **Eq. (10.1), p. 241, PDF p. 258, restricted to `{−1,+1}` labels (§10.2).** For a target
--   preference function $f:X\times X\to\mathbb R$ and scoring function $h:X\to\mathbb R$,
--   $R(h) = \Pr_{(x,x')\sim D}[f(x,x')(h(x')-h(x)) \le 0]$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Eq. (10.1), p. 241 (PDF p. 258)

import Mathlib

open MeasureTheory

namespace FoundationsML.Ranking

/-- The generalization error (pairwise misranking risk) of a scoring function
`h : X → ℝ` against a `{−1,+1}`-valued target preference function `f : X × X → ℝ`
and a distribution `D` over pairs `X × X` (Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, Eq. (10.1), p. 241, PDF p. 258, restricted to the
`{−1,+1}`-label case of §10.2): `R(h) = P_{(x,x')∼D}[f(x,x')(h(x') − h(x)) ≤ 0]`. -/
noncomputable def GeneralizationError {X : Type*} [MeasurableSpace X]
    (D : Measure (X × X)) (f : X × X → ℝ) (h : X → ℝ) : ℝ :=
  (D {p | f p * (h p.2 - h p.1) ≤ 0}).toReal

end FoundationsML.Ranking


