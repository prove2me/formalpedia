-- Prove2me | Definitions.Def_ManipPotential_IsTriangulationOf
-- name    : ManipPotential_IsTriangulationOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:42:43.623623+00:00
-- url     : https://prove2.me/theorems/5dfc7525-2fd6-4b8b-9b54-448a398c83a5
-- title:
--   Triangulation of a $d$-simplex
-- statement:
--   Let $S = \mathrm{conv}\{p_0, \dots, p_d\}$ be a $d$-simplex in a real vector space ($p_0, \dots, p_d$ affinely independent). A **triangulation** of $S$ is a finite collection of smaller $d$-simplices (its elementary simplices) whose union is $S$, where any two distinct simplices intersect in a common face or not at all.
--
--   **Formalization Note** Encoded as a finite geometric simplicial complex (closed under taking faces, any two faces meeting in a common face) whose underlying space is $S$ and in which every face is contained in a face with $d + 1$ vertices; the faces with $d + 1$ vertices are the elementary simplices.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, p.30 (before Lemma 6.8)

import Mathlib

namespace ManipPotential

/-- A triangulation of the `d`-simplex `S = conv {p_0, …, p_d}` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, p.30, before
Lemma 6.8): a finite collection of `d`-simplices whose union is `S`, any two of which meet in a common
face or not at all.

**Formalization Note** A finite geometric simplicial complex `K` (Mathlib's
`Geometry.SimplicialComplex`, closed under faces, any two faces meeting in a common face) whose
underlying space is `S` and in which every face lies in a face with `d + 1` vertices (the elementary
`d`-simplices). -/
def IsTriangulationOf {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (d : ℕ) (p : Fin (d + 1) → E) : Prop :=
  K.faces.Finite ∧ K.space = convexHull ℝ (Set.range p) ∧
    ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = d + 1

end ManipPotential


