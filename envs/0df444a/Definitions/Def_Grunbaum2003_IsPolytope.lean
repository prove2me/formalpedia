-- Prove2me | Definitions.Def_Grunbaum2003_IsPolytope
-- name    : Grunbaum2003_IsPolytope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:38:16.774986+00:00
-- url     : https://prove2.me/theorems/0521eb5e-ea47-47a6-9844-25816c1bb676
-- title:
--   Nonempty polytope of arbitrary affine dimension
-- statement:
--   A subset of real coordinate space that is the convex hull of a nonempty finite set, without requiring full affine dimension.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §3.1, printed p. 31 / PDF p. 51; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

namespace Grunbaum2003

/-- Nonempty polytopes of any affine dimension in real coordinate space.
This is the finite-hull component of the existing `IsDPolytope`, without
its full-dimensionality clause: summands can have smaller dimension.
Local expression-essential adapter, §3.1 and §15.1, printed pp.31,316. -/
def IsPolytope {d : ℕ} (P : Set (Fin d → ℝ)) : Prop :=
  ∃ V : Set (Fin d → ℝ), V.Finite ∧ V.Nonempty ∧ P = convexHull ℝ V

end Grunbaum2003


