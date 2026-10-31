-- Prove2me | Definitions.Def_LeastMajorized_subPolyhedron
-- name    : LeastMajorized_subPolyhedron
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:40.798427+00:00
-- url     : https://prove2.me/theorems/6f9e8892-7e4d-420e-9638-bae63493216c
-- title:
--   Submodular polyhedron $P(f)$
-- statement:
--   For $x\in\mathbb R^n$ and $S\subseteq N=\{1,\dots,n\}$ write $x(S):=\sum_{i\in S}x_i$. The **submodular polyhedron** of a set function $f:2^N\to\mathbb R$ is
--
--   $$
--   P(f):=\{x\in\mathbb R^n \mid x(A)\le f(A)\ \ \forall A\in 2^N\}.
--   $$
--
--   When $f$ is submodular this is the polyhedron whose maximal elements form the base polyhedron $B(f)$; Lemma 15 places the convex hull of a set inside $P(f)$.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`. The set is defined by the paper's formula for every $f$; submodularity is a hypothesis of the statements that use it.
-- source:
--   Schoot Uiterkamp, A characterization of simultaneous optimization, majorization, and (bi)submodular polyhedra, arXiv:2201.06596v2, §2.2, p.5 (x(S) from §2.1, p.4)

import Mathlib

namespace LeastMajorized

/-- **Submodular polyhedron** `P(f)`, Schoot Uiterkamp, arXiv:2201.06596v2, §2.2, p.5:
`P(f) := {x ∈ ℝⁿ | x(A) ≤ f(A) ∀ A ∈ 2^N}`, where `x(A) := Σ_{i∈A} xᵢ` (§2.1, p.4).

**Formalization Note** `ℝⁿ` is `Fin n → ℝ`, `2^N` is `Finset (Fin n)`. The set is defined for
every set function `f`, exactly by the paper's formula; submodularity of `f` is a hypothesis of
the theorems that use it. -/
def subPolyhedron {n : ℕ} (f : Finset (Fin n) → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ A : Finset (Fin n), ∑ i ∈ A, x i ≤ f A}

end LeastMajorized


