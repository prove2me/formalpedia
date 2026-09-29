-- Prove2me | Definitions.Def_ConeLifts_Factorization_SlackFactorizable
-- name    : ConeLifts_Factorization_SlackFactorizable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:43:44.080108+00:00
-- url     : https://prove2.me/theorems/17f5176f-a809-4c52-9e59-16b86a16b704
-- title:
--   The slack operator $S_C$ is $K$-factorizable
-- statement:
--   Let $C \subseteq \mathbb R^n$ and $K \subseteq \mathbb R^m$, and write $\operatorname{ext}(C)$ for the set of extreme points of $C$. The **slack operator** $S_C$ is the restriction of $S(x,y) = 1 - \langle x, y\rangle$ to $\operatorname{ext}(C) \times \operatorname{ext}(C^\circ)$. It is **$K$-factorizable** if there are maps, not necessarily linear,
--
--   $$
--   A : \operatorname{ext}(C) \to K, \qquad B : \operatorname{ext}(C^\circ) \to K^*,
--   $$
--
--   such that
--
--   $$
--   S_C(x,y) = 1 - \langle x, y\rangle = \langle A(x), B(y)\rangle \quad \text{for all } (x,y) \in \operatorname{ext}(C)\times\operatorname{ext}(C^\circ).
--   $$
--
--   This is the algebraic side of the paper; for a polytope and $K = \mathbb R^k_+$ it is a nonnegative factorization of the slack matrix.
--
--   **Formalization Note** $A$ and $B$ are total functions $\mathbb R^n \to \mathbb R^m$ constrained only on $\operatorname{ext}(C)$ and $\operatorname{ext}(C^\circ)$; their other values play no role, so this is equivalent to maps defined on the extreme points only. Extreme points are Mathlib's `Set.extremePoints ℝ`, $C^\circ$ is the one-sided polar and $K^*$ the dual cone of this mission. Both pairings are the Euclidean inner product.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 3 (slack operator) and p. 4, Definition 2.2

import Mathlib
import Definitions.Def_ConeLifts_Shared_polar
import Definitions.Def_ConeLifts_Shared_dualCone

open scoped InnerProductSpace

namespace ConeLifts.Factorization

/-- The **slack operator `S_C` of `C` is `K`-factorizable** (Gouveia, Parrilo & Thomas,
arXiv:1111.3164v2, §2 p. 3 and Definition 2.2, p. 4). The slack operator is the restriction of
`S(x, y) = 1 - ⟨x, y⟩` to `ext(C) × ext(C°)`; it is `K`-factorizable if there are maps (not
necessarily linear) `A : ext(C) → K` and `B : ext(C°) → K*` with `S_C(x, y) = ⟨A(x), B(y)⟩` for
all `(x, y) ∈ ext(C) × ext(C°)`.

`A` and `B` are total functions `ℝⁿ → ℝᵐ` constrained only on `ext(C)` resp. `ext(C°)`; their
values elsewhere are irrelevant, so this is equivalent to maps defined on the extreme points
only. `ext` is Mathlib's `Set.extremePoints ℝ`, `C°` is the one-sided `polar`, `K*` is
`dualCone K`, and both pairings are the Euclidean inner product. -/
def SlackFactorizable {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (C : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ A B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m),
    (∀ x ∈ Set.extremePoints ℝ C, A x ∈ K) ∧
    (∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), B y ∈ ConeLifts.Shared.dualCone K) ∧
    ∀ x ∈ Set.extremePoints ℝ C, ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C),
      1 - ⟪x, y⟫_ℝ = ⟪A x, B y⟫_ℝ

end ConeLifts.Factorization


