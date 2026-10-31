-- Prove2me | Definitions.Def_CombOpt_TotalUnimodularity_IsIntegralPolyhedron
-- name    : CombOpt_TotalUnimodularity_IsIntegralPolyhedron
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:59.719991+00:00
-- url     : https://prove2.me/theorems/75ba3ab7-2c58-4da1-a30d-d9b938571f55
-- title:
--   Integral polyhedron
-- statement:
--   A rational polyhedron $P\subseteq\mathbb R^n$ is **integral** if every nonempty face of $P$ contains an integral vector, i.e. a vector $z\in\mathbb Z^n$.
--
--   Since $P$ is a face of itself, an integral polyhedron that is nonempty contains an integral point; the empty polyhedron is integral. For a pointed polyhedron the condition says exactly that every vertex is integral. Integrality is what makes a linear program over $P$ have an integral optimal solution whenever it has an optimal solution, which is the bridge from integer programming to linear programming.
--
--   **Formalization Note** Faces are those of `IsFace`. An integral vector is the coordinatewise real cast of some `z : Fin n → ℤ`. The predicate is defined for any set; every polyhedron to which this mission applies it is defined by integer data and hence is rational, as the book requires.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.4, p. 219 (PDF p. 227)

import Mathlib
import Definitions.Def_CombOpt_TotalUnimodularity_IsFace

namespace CombOpt.TotalUnimodularity

/-- **Integral polyhedron.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.4,
p. 219 (PDF p. 227): "A rational polyhedron is called *integral* if every nonempty face contains
an integral vector."

`IsIntegralPolyhedron P` holds when every nonempty face `F` of `P` (in the sense of p. 204,
`IsFace`, which includes `P` itself) contains a vector all of whose coordinates are integers.

**Formalization Note.** An integral vector of `ℝⁿ` is the coordinatewise real cast of some
`z : Fin n → ℤ`. The predicate is stated for any set `P`; every polyhedron to which this
mission applies it is defined by integer (hence rational) data, so it is a rational polyhedron
as the book requires. The empty polyhedron is integral (it has no nonempty face). Faces, not
vertices, are used, exactly as in the book: the definition also covers polyhedra without
vertices. -/
def IsIntegralPolyhedron {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  ∀ F : Set (Fin n → ℝ), IsFace P F → F.Nonempty →
    ∃ z : Fin n → ℤ, (fun j => (z j : ℝ)) ∈ F

end CombOpt.TotalUnimodularity


