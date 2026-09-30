-- Prove2me | Definitions.Def_ConeLifts_StableSet_IsFacet
-- name    : ConeLifts_StableSet_IsFacet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:17:37.20528+00:00
-- url     : https://prove2.me/theorems/8f15e0e8-cf77-49c8-963d-8e236f1ab600
-- title:
--   Facet of a convex set: a nonempty proper exposed face of codimension one
-- statement:
--   Let $P \subseteq \mathbb R^n$ be a convex set. A subset $F$ is a **facet** of $P$ if
--
--   1. $F$ is an exposed face: $F = \{x \in P : \ell(x) = \max_{P} \ell\}$ for some linear functional $\ell$;
--   2. $F$ is nonempty and $F \ne P$;
--   3. $\dim F + 1 = \dim P$, where $\dim$ is the dimension of the affine hull.
--
--   For a polytope these are the maximal proper faces, the faces cut out by the irredundant inequalities of its description.
--
--   **Formalization Note** Exposedness is Mathlib's `IsExposed ℝ P F`; dimensions are `Module.finrank` of `vectorSpan`. Because $F$ is required to be nonempty and the dimensions are compared as $\dim F + 1 = \dim P$, neither the empty set nor truncated natural-number subtraction can produce a spurious facet.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 9, §3 (facets of a full-dimensional polytope) and p. 19, Theorem 5.2 (proof)

import Mathlib

namespace ConeLifts.StableSet

/-- `F` is a **facet** of the convex set `P ⊆ ℝⁿ` (the notion used in Gouveia, Parrilo & Thomas,
arXiv:1111.3164v2, §3, p. 9, and in the proof of Theorem 5.2, p. 19): `F` is a nonempty proper
exposed face of `P` (the set where some linear functional attains its maximum over `P`) whose
affine dimension is one less than that of `P`. Dimensions are compared as
`dim F + 1 = dim P` with `dim` the rank of the vector span; since `F` is required to be nonempty,
no truncated subtraction or empty-set convention is involved. -/
def IsFacet {n : ℕ} (P F : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsExposed ℝ P F ∧ F.Nonempty ∧ F ≠ P ∧
    Module.finrank ℝ (vectorSpan ℝ F) + 1 = Module.finrank ℝ (vectorSpan ℝ P)

end ConeLifts.StableSet


