-- Prove2me | Definitions.Def_ConeLifts_NonnegRank_nonnegRank
-- name    : ConeLifts_NonnegRank_nonnegRank
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:11:07.934899+00:00
-- url     : https://prove2.me/theorems/43c05758-47b6-4e9a-86cf-c25d52e04897
-- title:
--   Nonnegative rank $\operatorname{rank}_+(C)$ of a convex body
-- statement:
--   Let $C \subseteq \mathbb{R}^n$ and $k \in \mathbb{N}$. The slack operator of $C$ has an **$\mathbb{R}^k_+$-factorization** if there are maps $A : \operatorname{ext}(C) \to \mathbb{R}^k_+$ and $B : \operatorname{ext}(C^\circ) \to \mathbb{R}^k_+$ (not necessarily linear) such that
--
--   $$1 - \langle x, y\rangle = \langle A(x), B(y)\rangle = \sum_{i=1}^{k} A(x)_i\, B(y)_i \qquad \text{for all } x \in \operatorname{ext}(C),\ y \in \operatorname{ext}(C^\circ).$$
--
--   The **nonnegative rank** $\operatorname{rank}_+(C)$ is the smallest $k$ for which such a factorization exists, and $\operatorname{rank}_+(C) = +\infty$ if none exists.
--
--   The nonnegative rank of a polytope is the smallest $k$ such that it is the linear image of an affine slice of the nonnegative orthant $\mathbb{R}^k_+$, i.e. the size of its smallest linear-programming lift.
--
--   **Formalization Note** $A$ and $B$ are functions on all of $\mathbb{R}^n$ whose values are constrained only on the extreme points. The rank takes values in `ℕ∞`, as the infimum over all $k$ admitting a factorization; the infimum of the empty family is $\top = +\infty$. The cone $\mathbb{R}^k_+$ is self-dual, so this is the $K$-factorization of the paper with $K = K^* = \mathbb{R}^k_+$.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 13, Definition 4.3 (2) with K = (ℝⁱ₊); p. 4, Definition 2.2 (K-factorization)

import Mathlib
import Definitions.Def_ConeLifts_Shared_polar
import Definitions.Def_ConeLifts_NonnegRank_slackOperator

namespace ConeLifts.NonnegRank

/-- The slack operator of `C` has an **`ℝᵏ₊`-factorization** (Gouveia, Parrilo & Thomas,
arXiv:1111.3164v2, Definition 2.2 with `K = ℝᵏ₊ = K*`, and Definition 4.3, p. 13): there are maps
`A : ext(C) → ℝᵏ₊` and `B : ext(C°) → ℝᵏ₊` (not necessarily linear) with
`S_C(x, y) = 1 − ⟨x, y⟩ = ⟨A(x), B(y)⟩` for all `x ∈ ext(C)`, `y ∈ ext(C°)`.
`A`, `B` are total functions on `ℝⁿ`; only their values on the extreme points are constrained. -/
def HasNonnegFactorization {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) : Prop :=
  ∃ A B : EuclideanSpace ℝ (Fin n) → (Fin k → ℝ),
    (∀ x ∈ Set.extremePoints ℝ C, ∀ i, 0 ≤ A x i) ∧
    (∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), ∀ i, 0 ≤ B y i) ∧
    ∀ x ∈ Set.extremePoints ℝ C, ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C),
      slackOperator x y = ∑ i, A x i * B y i

/-- The **nonnegative rank** `rank₊(C)` of a convex body `C` (Gouveia, Parrilo & Thomas,
arXiv:1111.3164v2, Definition 4.3 (2) with `K = (ℝⁱ₊)`, p. 13): the smallest `i` such that the slack
operator `S_C` has an `ℝⁱ₊`-factorization, and `+∞` (`⊤ : ℕ∞`) if no such `i` exists. -/
noncomputable def nonnegRank {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : HasNonnegFactorization C k), (k : ℕ∞)

end ConeLifts.NonnegRank


