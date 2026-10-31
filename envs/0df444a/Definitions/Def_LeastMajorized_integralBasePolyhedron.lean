-- Prove2me | Definitions.Def_LeastMajorized_integralBasePolyhedron
-- name    : LeastMajorized_integralBasePolyhedron
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:23.677235+00:00
-- url     : https://prove2.me/theorems/09add96c-8a24-485c-b3e4-14f39dc1cc5d
-- title:
--   Integral base polyhedron $B^{\mathbb Z}(f)$
-- statement:
--   The **integral base polyhedron** of a set function $f:2^N\to\mathbb R$ is the set of integer-valued points of its base polyhedron:
--
--   $$
--   B^{\mathbb Z}(f):=B(f)\cap\mathbb Z^n .
--   $$
--
--   The paper introduces it for an integral submodular function $f$; it appears in the second sentence of Lemma 9.
--
--   **Formalization Note** $\mathbb Z^n$ is the set of vectors `x : Fin n → ℝ` whose entries are all integers, so $B^{\mathbb Z}(f)$ is a subset of `Fin n → ℝ`, as in the paper. Defined for every $f$; integrality and submodularity of $f$ are hypotheses of the statements that use it.
-- source:
--   Schoot Uiterkamp, A characterization of simultaneous optimization, majorization, and (bi)submodular polyhedra, arXiv:2201.06596v2, §2.2, p.5

import Mathlib
import Definitions.Def_LeastMajorized_basePolyhedron

namespace LeastMajorized

/-- **Integral base polyhedron** `B^ℤ(f)`, Schoot Uiterkamp, arXiv:2201.06596v2, §2.2, p.5:
`B^ℤ(f) := B(f) ∩ ℤⁿ`, the integer-valued points of the base polyhedron.

**Formalization Note** `ℤⁿ` is the set of vectors `x : Fin n → ℝ` with every entry an integer, so
`B^ℤ(f)` is a subset of `Fin n → ℝ`, as in the paper. The paper introduces it for an integral
submodular function `f`; the set is defined for every `f`, and integrality and submodularity of
`f` are hypotheses of the statements that use it. -/
def integralBasePolyhedron {n : ℕ} (f : Finset (Fin n) → ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ basePolyhedron f ∧ ∀ i, ∃ m : ℤ, x i = (m : ℝ)}

end LeastMajorized


