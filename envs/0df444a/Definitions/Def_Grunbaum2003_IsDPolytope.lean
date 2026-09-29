-- Prove2me | Definitions.Def_Grunbaum2003_IsDPolytope
-- name    : Grunbaum2003_IsDPolytope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:34:17.406143+00:00
-- url     : https://prove2.me/theorems/0137f555-c57e-413c-9803-d6e4986fb3b0
-- title:
--   Full dimensional nonempty polytope
-- statement:
--   A nonempty finite convex hull spanning real d-space.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §3.1, printed p. 31 / PDF p. 51; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false
namespace Grunbaum2003

/-- Full-dimensional nonempty polytopes in real coordinate space.
Grünbaum §3.1, p. 31: polytopes are equivalently finite convex hulls.
This is a local definition, not a published Prove2Me reference. -/
def IsDPolytope {d : ℕ} (P : Set (Fin d → ℝ)) : Prop :=
  (∃ V : Set (Fin d → ℝ), V.Finite ∧ V.Nonempty ∧ P = convexHull ℝ V) ∧
    affineSpan ℝ P = ⊤

end Grunbaum2003


