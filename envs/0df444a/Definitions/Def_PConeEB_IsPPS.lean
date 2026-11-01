-- Prove2me | Definitions.Def_PConeEB_IsPPS
-- name    : PConeEB_IsPPS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:57.267601+00:00
-- url     : https://prove2.me/theorems/fd342736-4ab7-4503-b983-8fed2af47bd6
-- title:
--   Partial-polyhedral Slater (PPS) condition
-- statement:
--   The problem (Feas) satisfies the **partial-polyhedral Slater (PPS) condition** if one of the following holds:
--
--   1. $K$ is polyhedral;
--   2. $(\mathcal L+a)\cap\operatorname{ri}K\ne\emptyset$ (Slater's condition);
--   3. $K=K^1\times K^2$ where $K^1$ is polyhedral and $(\mathcal L+a)\cap(K^1\times\operatorname{ri}K^2)\ne\emptyset$.
--
--   Under this condition a Lipschitzian error bound holds (Proposition 2.1).
--
--   **Formalization Note** The relative interior is `intrinsicInterior ℝ`. In the third alternative the product is an internal direct sum: $K^1\subseteq\mathcal E_1$, $K^2\subseteq\mathcal E_2$ for complementary subspaces, not required to be orthogonal, and $K$ is the set of sums $x_1+x_2$. Orthogonal subspaces give the Cartesian product.
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, §2, p.3

import Mathlib
import Definitions.Def_PConeEB_IsPolyhedralSet
import Definitions.Def_PConeEB_affineSet

namespace PConeEB

/-- The partial-polyhedral Slater (PPS) condition for (Feas): (i) `K` is polyhedral; or
(ii) `(L + a) ∩ ri K ≠ ∅`; or (iii) `K = K₁ × K₂` with `K₁` polyhedral and
`(L + a) ∩ (K₁ × ri K₂) ≠ ∅`. Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, §2, p.3.

**Formalization Note.** `ri` is `intrinsicInterior ℝ`. In (iii) the product is an internal direct
sum: `K₁ ⊆ E₁`, `K₂ ⊆ E₂` for complementary subspaces `E₁, E₂`, not necessarily orthogonal, and
`K₁ × K₂` is `{x₁ + x₂}`. An orthogonal decomposition is the special case that matches a Cartesian
product. -/
def IsPPS {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (L : Submodule ℝ E) (a : E) : Prop :=
  IsPolyhedralSet K ∨
    (affineSet L a ∩ intrinsicInterior ℝ K).Nonempty ∨
    ∃ (E₁ E₂ : Submodule ℝ E) (K₁ K₂ : Set E),
      IsCompl E₁ E₂ ∧ K₁ ⊆ (E₁ : Set E) ∧ K₂ ⊆ (E₂ : Set E) ∧
        K = {x | ∃ x₁ ∈ K₁, ∃ x₂ ∈ K₂, x = x₁ + x₂} ∧
        IsPolyhedralSet K₁ ∧
        ∃ x₁ ∈ K₁, ∃ x₂ ∈ intrinsicInterior ℝ K₂, x₁ + x₂ ∈ affineSet L a

end PConeEB


