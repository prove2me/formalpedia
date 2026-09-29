-- Prove2me | Definitions.Def_ConeLifts_Factorization_IsClosedConvexCone
-- name    : ConeLifts_Factorization_IsClosedConvexCone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:41:59.787061+00:00
-- url     : https://prove2.me/theorems/da31800b-ce4a-475b-8446-c346c89f32c9
-- title:
--   Closed convex cone in $\mathbb R^m$
-- statement:
--   A set $K \subseteq \mathbb R^m$ is a **closed convex cone** if it is topologically closed, convex, contains the origin, and is closed under nonnegative scaling:
--
--   $$
--   t \ge 0,\ x \in K \ \Longrightarrow\ t x \in K .
--   $$
--
--   Definition 2.1 of Gouveia, Parrilo and Thomas lifts convex bodies to affine slices of full-dimensional closed convex cones, such as the nonnegative orthant or the cone of positive semidefinite matrices.
--
--   **Formalization Note** Pointedness is not required, as in the paper. The paper's full-dimensionality of $K$ is the separate hypothesis $\operatorname{int} K \neq \emptyset$ in every theorem of the mission.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 3, Definition 2.1 (closed convex cone K)

import Mathlib

namespace ConeLifts.Factorization

/-- `K ⊆ ℝᵐ` is a **closed convex cone** (the class of cones of Gouveia, Parrilo & Thomas,
arXiv:1111.3164v2, Definition 2.1, p. 3): `K` is topologically closed, convex, contains the
origin, and is closed under multiplication by nonnegative scalars. Pointedness (salience) is not
required. Full-dimensionality, which Definition 2.1 also asks for, is the separate hypothesis
`(interior K).Nonempty`. -/
def IsClosedConvexCone {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) : Prop :=
  IsClosed K ∧ Convex ℝ K ∧ (0 : EuclideanSpace ℝ (Fin m)) ∈ K ∧
    ∀ t : ℝ, 0 ≤ t → ∀ x ∈ K, t • x ∈ K

end ConeLifts.Factorization


