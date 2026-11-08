-- Prove2me | Definitions.Def_FairFacilityLoc_penalty
-- name    : FairFacilityLoc_penalty
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:17.721201+00:00
-- url     : https://prove2.me/theorems/2e1c37fc-2ebe-4129-8303-0da862111a5f
-- title:
--   The penalty parameter $b_d$, (2.3)
-- statement:
--   $$b_d=(3-2\sqrt d)_+,\qquad b_1=1,\quad b_2=3-2\sqrt2,\quad b_3=0.$$
--
--   It weights the mass outside a set in the score of the Score-Balanced mechanism for $d\le3$.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), (2.3), p.16 (PDF p.18)

import Mathlib

namespace FairFacilityLoc

/-- The **penalty parameter** `b_d = (3 − 2√d)₊`, (2.3), p.16, PDF p.18 (Yan, Zhou, manuscript, sha256
642a1268…): `b₁ = 1`, `b₂ = 3 − 2√2`, `b₃ = 0`. -/
noncomputable def penalty (d : ℕ) : ℝ :=
  max (3 - 2 * √(d : ℝ)) 0

end FairFacilityLoc


