-- Prove2me | Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
-- name    : Grunbaum2003_IsSimplicialDPolytope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:21:08.648953+00:00
-- url     : https://prove2.me/theorems/d7ec3b44-f8e8-45a1-86df-d1004284b62c
-- title:
--   Simplicial full-dimensional polytope
-- statement:
--   A full-dimensional d-polytope every facet of which is the convex hull of d affinely independent vertices.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §4.5, printed p. 57 / PDF p. 81; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Mathlib.Analysis.Convex.Exposed
import Mathlib.LinearAlgebra.AffineSpace.Independent

set_option autoImplicit false
namespace Grunbaum2003

/-- §4.5, p.57: every facet is a simplex. A facet has dimension d-1,
expressed by `finrank + 1 = d` to avoid natural subtraction at d=0.
Its d vertices are affinely independent and their convex hull is the facet.
This local predicate reuses the book's full-dimensional polytope model. -/
def IsSimplicialDPolytope {d : ℕ} (P : Set (Fin d → ℝ)) : Prop :=
  IsDPolytope P ∧
    ∀ F : Set (Fin d → ℝ), F.Nonempty → IsExposed ℝ P F →
      Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d →
      ∃ v : Fin d → (Fin d → ℝ),
        AffineIndependent ℝ v ∧ F = convexHull ℝ (Set.range v)

end Grunbaum2003


