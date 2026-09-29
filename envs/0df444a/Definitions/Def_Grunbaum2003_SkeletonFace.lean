-- Prove2me | Definitions.Def_Grunbaum2003_SkeletonFace
-- name    : Grunbaum2003_SkeletonFace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:37:36.437492+00:00
-- url     : https://prove2.me/theorems/606c82db-7b13-49ed-b505-78fec99e8b4c
-- title:
--   Face poset of a skeleton
-- statement:
--   The empty face and all exposed faces whose affine dimension is at most k.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §12.3, printed p. 231 / PDF p. 273; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_PolytopeFace
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

namespace Grunbaum2003

/-- The face poset of the k-skeleton, with its inherited inclusion order.
The empty face is included explicitly (source dimension -1). For every
nonempty face the source dimension is the finrank of its affine direction.
This is an expression-essential local subtype, not a published definition. -/
abbrev SkeletonFace {d : ℕ} (P : Set (Fin d → ℝ)) (k : ℕ) :=
  {F : PolytopeFace P // F.val = ∅ ∨
    Module.finrank ℝ (affineSpan ℝ F.val).direction ≤ k}

end Grunbaum2003


