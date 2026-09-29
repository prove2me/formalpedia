-- Prove2me | Definitions.Def_Grunbaum2003_IsKNeighborly
-- name    : Grunbaum2003_IsKNeighborly
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:40:02.510764+00:00
-- url     : https://prove2.me/theorems/73fb4c86-f2a9-4bf1-beed-7d0d8357b797
-- title:
--   k-neighborly polytope
-- statement:
--   A positive integer k is a neighborliness level for P when every k-element set of vertices spans a proper exposed face having exactly those vertices.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §7.1, printed p. 122 / PDF p. 152; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

namespace Grunbaum2003

/-- The source's k-neighborliness (§7.1, p.122 / PDF152): every k-element
vertex subset is exactly the vertex set of its convex hull, a proper face.
This expression-essential local definition stores no rigidity conclusion. -/
def IsKNeighborly {d : ℕ} (k : ℕ) (P : Set (Fin d → ℝ)) : Prop :=
  0 < k ∧ ∀ V : Finset (Fin d → ℝ),
    (∀ x ∈ V, IsExposed ℝ P {x}) → V.card = k →
    IsExposed ℝ P (convexHull ℝ (V : Set (Fin d → ℝ))) ∧
    convexHull ℝ (V : Set (Fin d → ℝ)) ≠ P ∧
    {x | IsExposed ℝ (convexHull ℝ (V : Set (Fin d → ℝ))) {x}} =
      (V : Set (Fin d → ℝ))

end Grunbaum2003


