-- Prove2me | Definitions.Def_Grunbaum2003_IsZonotope
-- name    : Grunbaum2003_IsZonotope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T07:04:07.611975+00:00
-- url     : https://prove2.me/theorems/6a4a281b-2d8d-467e-aeb0-a758e5eb50fb
-- title:
--   Finite Minkowski sum of line segments
-- statement:
--   A set is a zonotope when it is a finite vector sum of closed line segments with arbitrary endpoints.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §15.1, printed p. 323 / PDF p. 373; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

/-- A finite vector sum of closed line segments, Grünbaum §15.1,
printed p.323 / PDF373. Arbitrary endpoints retain translations and
unequal segment lengths. This concrete local adapter contains no
reconstruction premise; full dimension is imposed separately. -/
def IsZonotope {d : ℕ} (P : Set (Fin d → ℝ)) : Prop :=
  ∃ (n : ℕ) (a b : Fin n → (Fin d → ℝ)),
    P = {x | ∃ y : Fin n → (Fin d → ℝ),
      (∀ i, y i ∈ segment ℝ (a i) (b i)) ∧ x = ∑ i, y i}

end Grunbaum2003


