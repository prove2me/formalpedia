-- Prove2me | Definitions.Def_Grunbaum2003_polytopeGraph
-- name    : Grunbaum2003_polytopeGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T07:03:53.941988+00:00
-- url     : https://prove2.me/theorems/365df820-2643-4625-b47f-cbf325f19a8c
-- title:
--   Graph of a polytope
-- statement:
--   The simple graph whose vertices are singleton exposed faces and whose distinct vertices are adjacent when they lie on a common one-dimensional exposed face.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §11.3, printed p. 212 / PDF p. 252; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_PolytopeVertex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

namespace Grunbaum2003

/-- The graph of P (§11.3, p.212 / PDF252). Distinct vertices are adjacent
when they belong to a common one-dimensional exposed face. `fromRel`
removes loops and symmetrizes this already symmetric co-incidence relation.
Membership of the two vertices ensures that the face is nonempty. -/
noncomputable def polytopeGraph {d : ℕ} (P : Set (Fin d → ℝ)) :
    SimpleGraph (PolytopeVertex P) :=
  SimpleGraph.fromRel (fun u v =>
    ∃ F : Set (Fin d → ℝ), IsExposed ℝ P F ∧
      Module.finrank ℝ (affineSpan ℝ F).direction = 1 ∧
      u.val ∈ F ∧ v.val ∈ F)

end Grunbaum2003


