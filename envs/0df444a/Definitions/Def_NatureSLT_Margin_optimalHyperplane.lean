-- Prove2me | Definitions.Def_NatureSLT_Margin_optimalHyperplane
-- name    : NatureSLT_Margin_optimalHyperplane
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:51:04.086073+00:00
-- url     : https://prove2.me/theorems/dfdd651b-514e-4b8f-bff5-93c3f917e598
-- title:
--   Canonical separating hyperplane (5.8), optimal hyperplane (5.9), support vectors and the dual functional W(α) (5.17)
-- statement:
--   Let $(x_1, y_1), \dots, (x_\ell, y_\ell)$ be training data with $x_i \in \mathbb R^n$ and $y_i \in \{+1, -1\}$. A hyperplane $(w \cdot x) - b = 0$ with $w \in \mathbb R^n$ and $b \in \mathbb R$ separates the data **in canonical form** if
--
--   $$y_i\,[(w \cdot x_i) - b] \ge 1, \qquad i = 1, \dots, \ell. \tag{5.8}$$
--
--   The same constraints appear as (5.11). The **optimal hyperplane** $(w_0, b_0)$ satisfies (5.8) and minimizes $\Phi(w) = \|w\|^2$ (5.9), the minimum being taken over both the vector $w$ and the scalar $b$. The functional $\tfrac12 (w \cdot w)$ of (5.10) has the same minimizers. The **support vectors** of a hyperplane $(w_0, b_0)$ are the training vectors for which equality is achieved in (5.11):
--
--   $$y_i\,[(x_i \cdot w_0) - b_0] = 1.$$
--
--   For coefficients $\alpha = (\alpha_1, \dots, \alpha_\ell)$, the **dual functional** is
--
--   $$W(\alpha) = \sum_{i=1}^{\ell} \alpha_i - \frac12 \sum_{i,j=1}^{\ell} \alpha_i \alpha_j y_i y_j (x_i \cdot x_j). \tag{5.17}$$
--
--   These are the objects of the construction of the optimal hyperplane in Sections 5.4.1 and 5.5.
--
--   **Formalization Note** The vectors are indexed by `Fin ℓ` and live in `EuclideanSpace ℝ (Fin n)`. The labels are real numbers; the theorems using these definitions assume $y_i \in \{+1, -1\}$. "Optimal hyperplane" is a predicate on a pair $(w_0, b_0)$: it holds for no pair when the data cannot be separated, and nothing here asserts that a minimizer exists. The support vectors form a finite set of indices.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, pp. 132–135, Eqs. (5.8), (5.9), (5.11), (5.17)

import Mathlib
open scoped InnerProductSpace

namespace NatureSLT.Margin

/-- The hyperplane `(w · x) − b = 0` separates the training data `(x₁, y₁), …, (x_ℓ, y_ℓ)` **in
canonical form** (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §5.4.1, p. 132,
(5.8); the same constraints are (5.11), p. 133):
`yᵢ[(w · xᵢ) − b] ≥ 1`, `i = 1, …, ℓ`. The vectors are indexed by `Fin ℓ`; the labels `yᵢ` are
real numbers, and the theorems using this definition assume `yᵢ ∈ {+1, −1}`. -/
def IsCanonicalSeparating {n ℓ : ℕ} (x : Fin ℓ → EuclideanSpace ℝ (Fin n)) (y : Fin ℓ → ℝ)
    (w : EuclideanSpace ℝ (Fin n)) (b : ℝ) : Prop :=
  ∀ i, 1 ≤ y i * (⟪w, x i⟫_ℝ - b)

/-- `(w₀, b₀)` is the **optimal hyperplane** in canonical form (Vapnik, *The Nature of Statistical
Learning Theory*, 2nd ed., §5.4.1, p. 132, (5.8)–(5.9)): it satisfies the conditions (5.8) and
minimizes `Φ(w) = ‖w‖²`, the minimum being taken with respect to both the vector `w` and the
scalar `b`. ((5.10) minimizes `½(w · w)` under (5.11), which has the same minimizers.) -/
def IsOptimalHyperplane {n ℓ : ℕ} (x : Fin ℓ → EuclideanSpace ℝ (Fin n)) (y : Fin ℓ → ℝ)
    (w₀ : EuclideanSpace ℝ (Fin n)) (b₀ : ℝ) : Prop :=
  IsCanonicalSeparating x y w₀ b₀ ∧
    ∀ (w : EuclideanSpace ℝ (Fin n)) (b : ℝ), IsCanonicalSeparating x y w b → ‖w₀‖ ^ 2 ≤ ‖w‖ ^ 2

/-- The **support vectors** of the hyperplane `(w₀, b₀)` (Vapnik, *The Nature of Statistical
Learning Theory*, 2nd ed., §5.5, p. 134): the indices `i` of the training vectors for which
equality is achieved in inequality (5.11), `yᵢ[(xᵢ · w₀) − b₀] = 1`. -/
noncomputable def supportVectors {n ℓ : ℕ} (x : Fin ℓ → EuclideanSpace ℝ (Fin n))
    (y : Fin ℓ → ℝ) (w₀ : EuclideanSpace ℝ (Fin n)) (b₀ : ℝ) : Finset (Fin ℓ) :=
  {i | y i * (⟪x i, w₀⟫_ℝ - b₀) = 1}

/-- The **dual functional** (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §5.5,
p. 135, (5.17)):
`W(α) = ∑_{i=1}^ℓ αᵢ − ½ ∑_{i,j=1}^ℓ αᵢ αⱼ yᵢ yⱼ (xᵢ · xⱼ)`. -/
noncomputable def dualW {n ℓ : ℕ} (x : Fin ℓ → EuclideanSpace ℝ (Fin n)) (y : Fin ℓ → ℝ)
    (α : Fin ℓ → ℝ) : ℝ :=
  ∑ i, α i - 1 / 2 * ∑ i, ∑ j, α i * α j * y i * y j * ⟪x i, x j⟫_ℝ

end NatureSLT.Margin


