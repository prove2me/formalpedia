-- Prove2me | Definitions.Def_Grunbaum2003_IsCubicalDPolytope
-- name    : Grunbaum2003_IsCubicalDPolytope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:38:11.829642+00:00
-- url     : https://prove2.me/theorems/9174dfd0-c34e-4fb4-99b5-4f6bcbccfb31
-- title:
--   Cubical full dimensional polytope
-- statement:
--   A full dimensional d-polytope whose every facet has a face poset isomorphic to that of a (d−1)-cube.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §9.4, printed p. 155 / PDF p. 189; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_standardCube

set_option autoImplicit false

namespace Grunbaum2003

/-- §9.4, p.155: every facet is a combinatorial (d−1)-cube.
Order isomorphism of full face posets expresses combinatorial equivalence;
it does not require metric or affine equivalence to a cube. Nonemptiness
excludes the empty face before the codimension-one test. -/
def IsCubicalDPolytope {d : ℕ} (P : Set (Fin d → ℝ)) : Prop :=
  IsDPolytope P ∧
    ∀ F : Set (Fin d → ℝ), F.Nonempty → IsExposed ℝ P F →
      Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d →
      Nonempty (PolytopeFace F ≃o PolytopeFace (standardCube (d - 1)))

end Grunbaum2003


