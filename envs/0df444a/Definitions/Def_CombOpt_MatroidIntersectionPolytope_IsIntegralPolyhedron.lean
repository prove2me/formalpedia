-- Prove2me | Definitions.Def_CombOpt_MatroidIntersectionPolytope_IsIntegralPolyhedron
-- name    : CombOpt_MatroidIntersectionPolytope_IsIntegralPolyhedron
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:03.560305+00:00
-- url     : https://prove2.me/theorems/0d92ac38-aba3-406b-926e-44634f12e42a
-- title:
--   Integral polyhedron
-- statement:
--   A rational polyhedron $P$ is **integral** if every nonempty face of $P$ contains an integral vector, i.e. a vector all of whose coordinates are integers.
--
--   For a polytope this says that every vertex is integral. Theorems 6.22, 6.29 and 8.20 all pass through this notion.
--
--   **Formalization Note** The predicate is stated for any set; the theorems apply it to rational polyhedra. The empty polyhedron is integral.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.4, p. 219 (PDF p. 227)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_IsFace

namespace CombOpt.MatroidIntersectionPolytope

/-- **Integral polyhedron.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.4, p. 219 (PDF p. 227): "A rational polyhedron is called integral if every nonempty
face contains an integral vector."

`IsIntegralPolyhedron P` holds when every nonempty face `F` of `P` (`IsFace`, which includes `P`
itself) contains a vector all of whose coordinates are integers.

**Formalization Note.** An integral vector is the coordinatewise real cast of some `z : n → ℤ`.
The predicate is stated for any set; the theorems apply it to rational polyhedra, as the book
does. The empty polyhedron is integral (it has no nonempty face). -/
def IsIntegralPolyhedron {n : Type*} [Fintype n] (P : Set (n → ℝ)) : Prop :=
  ∀ F : Set (n → ℝ), CombOpt.MatchingPolytope.IsFace P F → F.Nonempty → ∃ z : n → ℤ, (fun j => (z j : ℝ)) ∈ F

end CombOpt.MatroidIntersectionPolytope


