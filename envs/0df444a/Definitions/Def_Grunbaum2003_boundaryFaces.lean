-- Prove2me | Definitions.Def_Grunbaum2003_boundaryFaces
-- name    : Grunbaum2003_boundaryFaces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:38:28.020644+00:00
-- url     : https://prove2.me/theorems/75e2e69a-668e-4297-9a03-b009043d977d
-- title:
--   Boundary complex faces
-- statement:
--   The exposed faces of a polytope other than the polytope itself, retaining the empty face.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §11.1, printed p. 199 / PDF p. 239; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

namespace Grunbaum2003

/-- Boundary complex ℬ(P), Chapter 11, printed p.199 / PDF239.
As in the existing `PolytopeFace`, faces use Mathlib's exposed-face
convention. The empty face remains; only P itself is excluded. -/
def boundaryFaces {d : ℕ} (P : Set (Fin d → ℝ)) : Set (Set (Fin d → ℝ)) :=
  {F | IsExposed ℝ P F ∧ F ≠ P}

end Grunbaum2003


