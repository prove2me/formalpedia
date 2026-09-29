-- Prove2me | Definitions.Def_Grunbaum2003_skeletonEmbeddingDimension
-- name    : Grunbaum2003_skeletonEmbeddingDimension
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:39:40.5697+00:00
-- url     : https://prove2.me/theorems/482bdf28-ef27-423c-8e0b-195b9cb7b1c8
-- title:
--   Optimal skeleton embedding dimension
-- statement:
--   The common source value a(d,k)=b(d,k): d when d≤k+1, and otherwise the minimum of d−1 and 2k+1.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §11.1, Theorem 11.1.4, printed p. 201 / PDF p. 241; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Mathlib.Data.Nat.Basic

set_option autoImplicit false

namespace Grunbaum2003

/-- The common dimension a(d,k)=b(d,k) of Theorem 11.1.4,
printed p.201 / PDF241, used only for 1 ≤ k ≤ d.
This combines the four displayed source cases: d=k; d=k+1;
k+2≤d≤2k+2; d≥2k+2. The two latter formulas agree at d=2k+2. -/
def skeletonEmbeddingDimension (d k : ℕ) : ℕ :=
  if d ≤ k + 1 then d else min (d - 1) (2 * k + 1)

end Grunbaum2003


