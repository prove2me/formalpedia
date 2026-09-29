-- Prove2me | Definitions.Def_ConeLifts_Factorization_HasProperLift
-- name    : ConeLifts_Factorization_HasProperLift
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:43:03.147058+00:00
-- url     : https://prove2.me/theorems/fc3db1ec-582d-4ea9-af0f-e41595374089
-- title:
--   $C$ has a proper $K$-lift: the affine slice meets $\operatorname{int} K$
-- statement:
--   A $K$-lift $C = \pi(K \cap L)$ (affine subspace $L \subseteq \mathbb R^m$, linear map $\pi : \mathbb R^m \to \mathbb R^n$) is **proper** if $L$ intersects the interior of $K$:
--
--   $$
--   C = \pi(K\cap L), \qquad L \cap \operatorname{int} K \neq \emptyset .
--   $$
--
--   The predicate says that a proper $K$-lift exists. Properness is a Slater-type condition; it is the hypothesis of the forward half of Theorem 2.4.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 3, Definition 2.1 (proper K-lift)

import Mathlib

namespace ConeLifts.Factorization

/-- `C ⊆ ℝⁿ` **has a proper `K`-lift** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2,
Definition 2.1, p. 3): there are an affine subspace `L ⊆ ℝᵐ` and a linear map `π : ℝᵐ → ℝⁿ`
with `C = π(K ∩ L)` such that `L` intersects the interior of `K`. -/
def HasProperLift {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (C : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin m)))
    (π : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)),
    C = π '' (K ∩ (L : Set (EuclideanSpace ℝ (Fin m)))) ∧
      (interior K ∩ (L : Set (EuclideanSpace ℝ (Fin m)))).Nonempty

end ConeLifts.Factorization


