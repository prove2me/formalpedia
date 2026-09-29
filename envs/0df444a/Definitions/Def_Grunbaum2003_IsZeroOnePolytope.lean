-- Prove2me | Definitions.Def_Grunbaum2003_IsZeroOnePolytope
-- name    : Grunbaum2003_IsZeroOnePolytope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:36:57.832833+00:00
-- url     : https://prove2.me/theorems/ccbff4a7-d6b0-48d6-a22f-90adc9be808c
-- title:
--   Binary coordinate polytope
-- statement:
--   A convex hull of a subset of the binary cube in real d-space.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §4.9, printed p. 69a / PDF p. 94; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

namespace Grunbaum2003

def IsZeroOnePolytope {d : ℕ} (P : Set (Fin d → ℝ)) : Prop :=
  ∃ V : Set (Fin d → ℝ),
    (∀ x ∈ V, ∀ i, x i = 0 ∨ x i = 1) ∧ P = convexHull ℝ V

end Grunbaum2003


