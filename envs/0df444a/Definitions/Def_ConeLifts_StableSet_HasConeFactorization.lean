-- Prove2me | Definitions.Def_ConeLifts_StableSet_HasConeFactorization
-- name    : ConeLifts_StableSet_HasConeFactorization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:17:10.852846+00:00
-- url     : https://prove2.me/theorems/2d88155f-bcb8-4f69-b85d-004fa92fec94
-- title:
--   $K$-factorization of a matrix: $M_{ij} = \langle a^i, b^j\rangle$ with $a^i \in K$, $b^j \in K^*$
-- statement:
--   Let $M = (M_{ij})$ be a real matrix and $K \subseteq \mathbb R^m$ a closed convex cone. A **$K$-factorization** of $M$ is a family of vectors $a^i \in K$, one for each row, and $b^j \in K^*$, one for each column, such that
--
--   $$
--   \langle a^i, b^j \rangle = M_{ij} \quad \text{for all } i, j.
--   $$
--
--   For $K = \mathbb R^k_+$ this is a nonnegative factorization $M = AB$ with $A$, $B$ nonnegative of inner dimension $k$.
--
--   **Formalization Note** Rows and columns may be indexed by arbitrary types (for slack matrices: vertices of $P$ and extreme points of $P^\circ$). $K^*$ is `dualCone K` and the pairing is the Euclidean inner product on `EuclideanSpace ℝ (Fin m)`. The paper states the definition for nonnegative matrices; the predicate is stated for all real matrices and is applied only to slack matrices, which are nonnegative.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 9, Definition 3.2

import Mathlib
import Definitions.Def_ConeLifts_Shared_dualCone

open scoped InnerProductSpace

namespace ConeLifts.StableSet

/-- A **`K`-factorization** of a matrix `M` (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2,
Definition 3.2, p. 9): vectors `aⁱ ∈ K` (one per row) and `bʲ ∈ K*` (one per column) with
`⟨aⁱ, bʲ⟩ = M_ij` for all `i, j`. Rows and columns are indexed by arbitrary types `ι`, `κ`
(for a slack matrix: the vertices of `P` and the extreme points of `P°`); `K*` is `dualCone K`
and the pairing is the Euclidean inner product of `EuclideanSpace ℝ (Fin m)`. -/
def HasConeFactorization {m : ℕ} {ι κ : Type*} (K : Set (EuclideanSpace ℝ (Fin m)))
    (M : Matrix ι κ ℝ) : Prop :=
  ∃ (a : ι → EuclideanSpace ℝ (Fin m)) (b : κ → EuclideanSpace ℝ (Fin m)),
    (∀ i, a i ∈ K) ∧ (∀ j, b j ∈ ConeLifts.Shared.dualCone K) ∧ ∀ i j, ⟪a i, b j⟫_ℝ = M i j

end ConeLifts.StableSet


