-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_IsProperFace
-- name    : CombOpt_MatchingPolytope_IsProperFace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:07:16.357129+00:00
-- url     : https://prove2.me/theorems/d52e18ab-3a41-45b1-a4d2-2e735b5d4057
-- title:
--   A proper face of a polyhedron
-- statement:
--   A **proper face** of a polyhedron $P$ is a face $F$ of $P$ other than the two conventional faces: $F\ne\emptyset$ and $F\ne P$.
--
--   Facets are the maximal proper faces.
--
--   **Formalization Note** The book says: "By convention, we also call the null set and the polyhedron itself faces, and we refer to the other faces as proper faces." This is read literally: a proper face is neither $\emptyset$ nor $P$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.2, p. 204 (PDF p. 212)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_IsFace

namespace CombOpt.MatchingPolytope

/-- **A proper face.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.2, p. 204 (PDF p. 212): "By convention, we also call the null set and the polyhedron
itself faces, and we refer to the other faces as proper faces."

`IsProperFace P F` says that `F` is a face of `P` other than `∅` and `P`.

**Formalization Note.** "The other faces" are read as the faces that are neither `∅` nor `P`.
Under the alternative reading (`∅` proper) the empty set would be a facet of every affine
subspace, and Corollary 6.19 (p. 213) would fail for `P = ℝ^n` defined by the empty system. -/
def IsProperFace {ι : Type*} [Fintype ι] (P F : Set (ι → ℝ)) : Prop :=
  IsFace P F ∧ F.Nonempty ∧ F ≠ P

end CombOpt.MatchingPolytope


