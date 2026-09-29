-- Prove2me | Definitions.Def_ConeLifts_Factorization_HasLift
-- name    : ConeLifts_Factorization_HasLift
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:42:41.977097+00:00
-- url     : https://prove2.me/theorems/74c0b54c-d452-4edd-bc32-e6a269405c40
-- title:
--   $C$ has a $K$-lift: $C = \pi(K \cap L)$ for an affine $L$ and a linear $\pi$
-- statement:
--   Let $K \subseteq \mathbb R^m$ and $C \subseteq \mathbb R^n$. A **$K$-lift** of $C$ is a set $Q = K \cap L$, where $L \subseteq \mathbb R^m$ is an affine subspace, together with a linear map $\pi : \mathbb R^m \to \mathbb R^n$ such that
--
--   $$
--   C = \pi(K \cap L).
--   $$
--
--   The predicate says that such $L$ and $\pi$ exist. Lifts are the geometric side of the paper: a convex body with a small $K$-lift can be optimized over by conic programming over $K$.
--
--   **Formalization Note** $L$ is a Mathlib `AffineSubspace` and $\pi$ a linear map; $C = \pi(K\cap L)$ is equality of sets. The standing assumptions of Definition 2.1 ($K$ a full-dimensional closed convex cone, $C$ a convex body) are hypotheses of the theorems that use the predicate.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 3, Definition 2.1 (K-lift)

import Mathlib

namespace ConeLifts.Factorization

/-- `C ⊆ ℝⁿ` **has a `K`-lift** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, Definition 2.1,
p. 3): there are an affine subspace `L ⊆ ℝᵐ` and a *linear* map `π : ℝᵐ → ℝⁿ` with
`C = π(K ∩ L)`; the set `Q = K ∩ L` is then a `K`-lift of `C`. The standing hypotheses of
Definition 2.1 on `K` (full-dimensional closed convex cone) and `C` (convex body) are carried by
the theorems that use this predicate. -/
def HasLift {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) (C : Set (EuclideanSpace ℝ (Fin n))) :
    Prop :=
  ∃ (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin m)))
    (π : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)),
    C = π '' (K ∩ (L : Set (EuclideanSpace ℝ (Fin m))))

end ConeLifts.Factorization


