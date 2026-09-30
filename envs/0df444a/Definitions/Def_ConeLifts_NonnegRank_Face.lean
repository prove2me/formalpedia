-- Prove2me | Definitions.Def_ConeLifts_NonnegRank_Face
-- name    : ConeLifts_NonnegRank_Face
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:10:24.393357+00:00
-- url     : https://prove2.me/theorems/7abfb2a9-322d-4d4a-bea5-b6955b87f294
-- title:
--   Face lattice $L(C)$: faces of $C$ ordered by inclusion
-- statement:
--   Let $C \subseteq \mathbb{R}^n$. A **face** of $C$ is a subset $F \subseteq C$ that is either empty or of the form
--
--   $$F = \{\, x \in C : \ell(x) = \max_{y \in C} \ell(y) \,\}$$
--
--   for some linear functional $\ell$ on $\mathbb{R}^n$ (an exposed face). The **face lattice** $L(C)$ is the set of faces of $C$ ordered by inclusion.
--
--   Both $\emptyset$ and $C$ itself (take $\ell = 0$) are faces. For a polytope every face in the usual sense is exposed, so this is the face lattice of the paper; its size counts all faces including $\emptyset$ and $C$: a square has $4 + 4 + 1 + 1 = 10$ faces and a three-dimensional cube $8 + 12 + 6 + 1 + 1 = 28$.
--
--   **Formalization Note** `Face C` is the subtype of sets $F$ with `IsExposed ℝ C F` (Mathlib's exposed faces, whose definition includes $\emptyset$ vacuously), with the partial order of set inclusion inherited from `Set`.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 15, §4.2 (face lattice L(C)); p. 16 (face counts 10 and 28)

import Mathlib

namespace ConeLifts.NonnegRank

/-- The **face lattice** `L(C)` of a polytope `C ⊆ ℝⁿ` (Gouveia, Parrilo & Thomas,
arXiv:1111.3164v2, §4.2, p. 15): the faces of `C` ordered by inclusion. A face is an exposed face in
Mathlib's sense (`IsExposed ℝ C F`: `F` is empty or `F = {x ∈ C | l x = max_C l}` for a continuous
linear functional `l`); for a polytope every face is exposed. The empty face and `C` itself (via
`l = 0`) are faces, as in the paper's face counts (a square has 10 faces, a 3-cube 28, p. 16).
The order is inclusion of the underlying sets (the subtype order of `Set`). -/
def Face {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) : Type :=
  {F : Set (EuclideanSpace ℝ (Fin n)) // IsExposed ℝ C F}

/-- Faces are ordered by inclusion. -/
instance {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) : PartialOrder (Face C) :=
  inferInstanceAs (PartialOrder {F : Set (EuclideanSpace ℝ (Fin n)) // IsExposed ℝ C F})

end ConeLifts.NonnegRank


