-- Prove2me | Definitions.Def_Grunbaum2003_skeletonCarrier
-- name    : Grunbaum2003_skeletonCarrier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:39:08.259824+00:00
-- url     : https://prove2.me/theorems/6b53e3a1-1743-451f-ab8c-c057086bc5c5
-- title:
--   Carrier of a polytope skeleton
-- statement:
--   The union of all exposed faces of a polytope having affine dimension at most k.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §11.1, printed p. 199 / PDF p. 239; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_SkeletonFace

set_option autoImplicit false

namespace Grunbaum2003

/-- Carrier of the k-skeleton, §11.1 p.199 / PDF239. Reuses the existing
face-poset subtype, including the empty face and all faces of dimension ≤ k. -/
def skeletonCarrier {d : ℕ} (P : Set (Fin d → ℝ)) (k : ℕ) :
    Set (Fin d → ℝ) :=
  {x | ∃ F : SkeletonFace P k, x ∈ F.val.val}

end Grunbaum2003


