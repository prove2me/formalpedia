-- Prove2me | Definitions.Def_ConeLifts_Shared_dualCone
-- name    : ConeLifts_Shared_dualCone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:42:21.135992+00:00
-- url     : https://prove2.me/theorems/1ad4621a-10db-4abb-8f73-8cb2832395b3
-- title:
--   Dual cone $K^* = \{y : \langle x, y\rangle \ge 0 \ \forall x \in K\}$
-- statement:
--   The **dual** of a set $K \subseteq \mathbb R^m$ is
--
--   $$
--   K^* = \{\, y \in \mathbb R^m : \langle x, y\rangle \ge 0 \ \text{ for all } x \in K \,\},
--   $$
--
--   with the Euclidean inner product. The paper uses it for closed convex cones $K$; the cones $\mathbb R^n_+$ and $\mathcal S^k_+$ are self-dual. In a $K$-factorization the second factor (the column factors) takes values in $K^*$.
--
--   This definition is shared by two missions of this series: I (the factorization theorem: Definition 2.2, p. 4, and the proof of Theorem 2.4, pp. 4–5) and III (stable set polytopes without psd lifts: Definition 3.2, p. 9).
--
--   **Formalization Note** $\mathbb R^m$ is `EuclideanSpace ℝ (Fin m)`. Defined locally: the platform's `ConvexOptimization.dualCone` has no module in this series' Lean environment.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 3, §2 (dual of a closed convex cone)

import Mathlib

open scoped InnerProductSpace

namespace ConeLifts.Shared

/-- The **dual cone** of `K ⊆ ℝᵐ` (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, §2, p. 3):
`K* = {y ∈ ℝᵐ : ⟨x, y⟩ ≥ 0 for all x ∈ K}`, with `⟨·,·⟩` the Euclidean inner product of
`EuclideanSpace ℝ (Fin m)`. -/
def dualCone {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) : Set (EuclideanSpace ℝ (Fin m)) :=
  {y | ∀ x ∈ K, 0 ≤ ⟪x, y⟫_ℝ}

end ConeLifts.Shared


