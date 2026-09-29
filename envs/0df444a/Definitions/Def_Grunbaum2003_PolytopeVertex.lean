-- Prove2me | Definitions.Def_Grunbaum2003_PolytopeVertex
-- name    : Grunbaum2003_PolytopeVertex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T07:03:34.66222+00:00
-- url     : https://prove2.me/theorems/4d842f88-1fb0-4e5f-92e6-236194dff29c
-- title:
--   Vertices as singleton exposed faces
-- statement:
--   The vertices of a body are the points whose singleton sets are exposed faces.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §§2.4, 11.3, printed pp. 17, 212 / PDF pp. 35, 252; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

namespace Grunbaum2003

/-- Vertices of P: points whose singleton is an exposed face.
For polytopes these are exactly the zero-dimensional faces.
Local expression-essential adapter for the 1-skeleton of §11.3, p.212. -/
def PolytopeVertex {d : ℕ} (P : Set (Fin d → ℝ)) :=
  {x : Fin d → ℝ // IsExposed ℝ P {x}}

end Grunbaum2003


