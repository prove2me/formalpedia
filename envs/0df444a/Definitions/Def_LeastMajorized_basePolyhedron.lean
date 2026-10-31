-- Prove2me | Definitions.Def_LeastMajorized_basePolyhedron
-- name    : LeastMajorized_basePolyhedron
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:48:41.839999+00:00
-- url     : https://prove2.me/theorems/63ebe400-f5d4-4e72-bdc0-80d0c7acd14b
-- title:
--   Base polyhedron $B(f)$
-- statement:
--   The **base polyhedron** of a set function $f:2^N\to\mathbb R$ is the face of the submodular polyhedron on which the total is maximal:
--
--   $$
--   B(f):=\{x\in P(f)\mid x(N)=f(N)\}.
--   $$
--
--   The mission's goal (Theorem 5) says that, among compact convex sets, base polyhedra of submodular functions are exactly the sets that have a least $(a,b)$-majorized element for every scaling $a$ and shift $b$.
--
--   **Formalization Note** $N$ is `Finset.univ : Finset (Fin n)`. Defined for every $f$; submodularity is a hypothesis of the statements that use it.
-- source:
--   Schoot Uiterkamp, A characterization of simultaneous optimization, majorization, and (bi)submodular polyhedra, arXiv:2201.06596v2, §2.2, p.5

import Mathlib
import Definitions.Def_LeastMajorized_subPolyhedron

namespace LeastMajorized

/-- **Base polyhedron** `B(f)`, Schoot Uiterkamp, arXiv:2201.06596v2, §2.2, p.5:
`B(f) := {x ∈ P(f) | x(N) = f(N)}`, with `N = {1, …, n}` the whole ground set.

**Formalization Note** `N` is `Finset.univ : Finset (Fin n)`. Defined for every set function
`f`; submodularity is a hypothesis of the theorems that use it. -/
def basePolyhedron {n : ℕ} (f : Finset (Fin n) → ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ subPolyhedron f ∧ ∑ i, x i = f Finset.univ}

end LeastMajorized


