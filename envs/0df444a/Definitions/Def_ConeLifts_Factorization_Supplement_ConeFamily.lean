-- Prove2me | Definitions.Def_ConeLifts_Factorization_Supplement_ConeFamily
-- name    : ConeLifts_Factorization_Supplement_ConeFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:42:24.597459+00:00
-- url     : https://prove2.me/theorems/d039a18e-ccf4-431f-b181-883fb792969d
-- title:
--   Cone family $(K_i)_{i \in \mathbb N}$ and closed cone family
-- statement:
--   A **cone family** $\mathcal K = (K_i)_{i \in \mathbb N}$ is a sequence, indexed by $i = 0, 1, 2, \dots$, of full-dimensional closed convex cones $K_i \subseteq \mathbb R^{m_i}$. The family is **closed** if for every $i$ and every face $F$ of $K_i$ there is $j \le i$ such that $F$ is isomorphic to $K_j$:
--
--   $$
--   F = T(K_j) \quad \text{for some injective linear map } T : \mathbb R^{m_j} \to \mathbb R^{m_i}.
--   $$
--
--   The nonnegative orthants $(\mathbb R^i_+)$ and the positive semidefinite cones $(\mathcal S^i_+)$ form closed families; the copositive cones do not. Closed families are the setting in which the cone rank of a convex body measures the smallest lift.
--
--   **Formalization Note** A face of $K_i$ is a nonempty convex extreme subset (Mathlib's `IsExtreme`). Full-dimensionality of each $K_i$ ($\operatorname{int} K_i \neq \emptyset$) is the standing requirement of Definitions 2.1 and 2.2, which Definition 4.3 applies to each $K_i$.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 12, Definition 4.1

import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsClosedConvexCone

namespace ConeLifts.Factorization.Supplement

/-- A **cone family** `𝒦 = (Kᵢ)_{i ∈ ℕ}` (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2,
Definition 4.1, p. 12): a sequence, indexed by `i = 0, 1, 2, …`, of closed convex cones
`Kᵢ ⊆ ℝ^{mᵢ}`. Each `Kᵢ` is full-dimensional (`int Kᵢ ≠ ∅`), the standing requirement of
Definitions 2.1 and 2.2 (p. 3–4) under which Definition 4.3 speaks of `Kᵢ`-factorizations and
`Kᵢ`-lifts. -/
structure ConeFamily where
  /-- The ambient dimension `mᵢ` of the `i`-th cone. -/
  dim : ℕ → ℕ
  /-- The `i`-th cone `Kᵢ ⊆ ℝ^{mᵢ}`. -/
  cone : (i : ℕ) → Set (EuclideanSpace ℝ (Fin (dim i)))
  /-- Each `Kᵢ` is a closed convex cone. -/
  isClosedConvexCone : ∀ i, ConeLifts.Factorization.IsClosedConvexCone (cone i)
  /-- Each `Kᵢ` is full-dimensional. -/
  interior_nonempty : ∀ i, (interior (cone i)).Nonempty

/-- A cone family is **closed** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, Definition 4.1,
p. 12) if for every `i` and every face `F` of `Kᵢ` there is `j ≤ i` such that `F` is isomorphic to
`Kⱼ`. A face of `Kᵢ` is a nonempty convex extreme subset of `Kᵢ` (Mathlib's `IsExtreme`); `F` is
isomorphic to `Kⱼ` if an injective linear map `T : ℝ^{mⱼ} → ℝ^{mᵢ}` carries `Kⱼ` onto `F`. -/
def ConeFamily.IsClosed (𝒦 : ConeFamily) : Prop :=
  ∀ i, ∀ F : Set (EuclideanSpace ℝ (Fin (𝒦.dim i))),
    F.Nonempty → Convex ℝ F → IsExtreme ℝ (𝒦.cone i) F →
      ∃ j ≤ i, ∃ T : EuclideanSpace ℝ (Fin (𝒦.dim j)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (𝒦.dim i)),
        Function.Injective T ∧ T '' 𝒦.cone j = F

end ConeLifts.Factorization.Supplement


