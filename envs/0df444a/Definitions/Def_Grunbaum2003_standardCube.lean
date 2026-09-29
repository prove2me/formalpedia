-- Prove2me | Definitions.Def_Grunbaum2003_standardCube
-- name    : Grunbaum2003_standardCube
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:37:52.568893+00:00
-- url     : https://prove2.me/theorems/ac7ab728-ae29-4971-a8c2-4eaf1f7ed612
-- title:
--   Standard unit cube
-- statement:
--   The Cartesian product of n closed unit intervals in real n-space.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §4.9, printed p. 69b / PDF p. 95; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

namespace Grunbaum2003

/-- Concrete reference cube [0,1]^n for combinatorial equivalence.
Its full exposed-face poset is supplied by the existing `PolytopeFace`.
This is a local expression adapter, not a published reference. -/
def standardCube (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

end Grunbaum2003


