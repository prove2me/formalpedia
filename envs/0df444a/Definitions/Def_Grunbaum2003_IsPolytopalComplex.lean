-- Prove2me | Definitions.Def_Grunbaum2003_IsPolytopalComplex
-- name    : Grunbaum2003_IsPolytopalComplex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:39:29.965079+00:00
-- url     : https://prove2.me/theorems/9e60a07e-563d-4e3d-8df2-edd9b7474f4c
-- title:
--   Finite polytopal complex
-- statement:
--   A finite family of polytopal cells, explicitly allowing the empty cell, that is closed under faces and whose pairwise intersections are faces of both cells.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §11.1, complex definition, printed p. 199 / PDF p. 239; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_IsPolytope
import Mathlib.Analysis.Convex.Exposed

set_option autoImplicit false

namespace Grunbaum2003

/-- A finite polytopal complex in real m-space, §11.1 p.199 / PDF239.
The empty face is admitted explicitly because the reused `IsPolytope`
means nonempty polytope. Cells may have any affine dimension. Closure
under faces and the common-face intersection condition are both retained. -/
def IsPolytopalComplex {m : ℕ} (C : Set (Set (Fin m → ℝ))) : Prop :=
  C.Finite ∧
    (∀ F ∈ C, F = ∅ ∨ IsPolytope F) ∧
    (∀ F ∈ C, ∀ G : Set (Fin m → ℝ), IsExposed ℝ F G → G ∈ C) ∧
    (∀ F ∈ C, ∀ G ∈ C,
      IsExposed ℝ F (F ∩ G) ∧ IsExposed ℝ G (F ∩ G))

end Grunbaum2003


