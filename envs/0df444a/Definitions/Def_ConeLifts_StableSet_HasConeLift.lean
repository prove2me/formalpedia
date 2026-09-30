-- Prove2me | Definitions.Def_ConeLifts_StableSet_HasConeLift
-- name    : ConeLifts_StableSet_HasConeLift
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:15:16.592112+00:00
-- url     : https://prove2.me/theorems/5442bcb9-011c-4e7a-90d3-25131245e452
-- title:
--   Cone lift: $C = \pi(K \cap L)$ with $L$ affine and $\pi$ linear (proper if $L$ meets $\mathrm{int}\,K$)
-- statement:
--   Let $K$ be a subset of a real vector space $U$ (in the paper, a full-dimensional closed convex cone) and $C$ a subset of a real vector space $W$. A **$K$-lift** of $C$ is a set $Q = K \cap L$, where $L \subseteq U$ is an affine subspace, together with a linear map $\pi : U \to W$ such that
--
--   $$
--   C = \pi(K \cap L).
--   $$
--
--   The lift is **proper** if $L$ intersects the interior of $K$. The predicates say that such $L$ and $\pi$ exist.
--
--   A lift turns linear optimization over $C$ into conic optimization over an affine slice of $K$; for $K$ a nonnegative orthant this is linear programming, for $K$ a cone of positive semidefinite matrices it is semidefinite programming.
--
--   **Formalization Note** Two predicates are defined: `HasConeLift K C` and `HasProperConeLift K C` (the latter needs a topology on $U$ for the interior). They are stated for arbitrary real vector spaces so that they apply both to cones in $\mathbb R^m$ and to the cone of positive semidefinite matrices. The equality $C = \pi(K\cap L)$ is equality of sets, not inclusion. The standing hypotheses of Definition 2.1 on $K$ and $C$ are carried by the theorems that use the predicates.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 3, Definition 2.1

import Mathlib

namespace ConeLifts.StableSet

/-- `C` **has a `K`-lift** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, Definition 2.1, p. 3):
there are an affine subspace `L` of the ambient space of `K` and a *linear* map `π` with
`C = π(K ∩ L)` (equality of sets); `Q = K ∩ L` is then a `K`-lift of `C`. The paper's standing
hypotheses on `K` (full-dimensional closed convex cone) and on `C` are carried by the theorems
that use this predicate; the predicate itself is stated for arbitrary real vector spaces so that
it covers both `K ⊆ ℝᵐ` and the cone of positive semidefinite matrices. -/
def HasConeLift {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (K : Set V) (C : Set W) : Prop :=
  ∃ (L : AffineSubspace ℝ V) (π : V →ₗ[ℝ] W), C = π '' (K ∩ (L : Set V))

/-- `C` **has a proper `K`-lift** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, Definition 2.1,
p. 3): a `K`-lift `C = π(K ∩ L)` whose affine subspace `L` intersects the interior of `K`. -/
def HasProperConeLift {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [AddCommGroup W] [Module ℝ W] (K : Set V) (C : Set W) : Prop :=
  ∃ (L : AffineSubspace ℝ V) (π : V →ₗ[ℝ] W),
    C = π '' (K ∩ (L : Set V)) ∧ ((L : Set V) ∩ interior K).Nonempty

end ConeLifts.StableSet


