-- Prove2me | Definitions.Def_NatureSLT_Margin_marginVCDim
-- name    : NatureSLT_Margin_marginVCDim
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:51:05.500999+00:00
-- url     : https://prove2.me/theorems/6450fc9e-50ec-4493-86b8-9d0d5529290d
-- title:
--   Δ-margin separating hyperplanes, shattering by them, and their VC dimension
-- statement:
--   Let $X \subseteq \mathbb R^n$ be a set of vectors and $\Delta$ a real number. A hyperplane
--
--   $$(w^* \cdot x) - b = 0, \qquad |w^*| = 1,\ b \in \mathbb R,$$
--
--   is a **$\Delta$-margin separating hyperplane** if it classifies vectors $x$ as follows:
--
--   $$y = \begin{cases} \phantom{-}1 & \text{if } (w^* \cdot x) - b \ge \Delta, \\ -1 & \text{if } (w^* \cdot x) - b \le -\Delta. \end{cases}$$
--
--   Vectors in the strip $|(w^* \cdot x) - b| < \Delta$ receive no label.
--
--   Vectors $x_1, \dots, x_h$ are **shattered by the $\Delta$-margin separating hyperplanes** if for each of the $2^h$ labelings $y_1, \dots, y_h \in \{1, -1\}$ there is a hyperplane $(w^*, b)$ with $|w^*| = 1$ that classifies every $x_i$ with the label $y_i$ in the sense above, so that no $x_i$ lies in its strip. The **VC dimension of the set of $\Delta$-margin separating hyperplanes on $X$** is the maximum number $h$ of vectors $x_1, \dots, x_h \in X$ that are shattered in this sense. It is infinite if shattered families of every size exist:
--
--   $$h(X, \Delta) = \sup\{h \in \mathbb N : \text{some } x_1, \dots, x_h \in X \text{ are shattered by the } \Delta\text{-margin separating hyperplanes}\} \in \mathbb N \cup \{\infty\}.$$
--
--   This is the capacity notion of Theorem 5.1. Unlike the ordinary VC dimension of separating hyperplanes ($n + 1$), it can be much smaller than $n + 1$ when $\Delta$ is large compared with the size of $X$.
--
--   **Formalization Note** Labels are booleans, `true` standing for $1$ and `false` for $-1$. The vectors are indexed by `Fin h` and may repeat; a repeated vector is never shattered when $\Delta > 0$. The VC dimension is an extended natural number, so an unbounded supremum is $\infty$. In dimension $n = 0$ there is no unit vector $w^*$, so nothing is shattered and the value is $0$. The vectors are elements of `EuclideanSpace ℝ (Fin n)`, and the inner product $(w^* \cdot x)$ is the Euclidean one.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 132, Section 5.4.2 (with the VC dimension of Section 3.6, p. 80)

import Mathlib
open scoped InnerProductSpace

namespace NatureSLT.Margin

/-- The hyperplane `(w* · x) − b = 0` **classifies `x` with label `y` at margin `Δ`** in the sense
of a Δ-margin separating hyperplane (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed.,
§5.4.2, p. 132): `y = 1` if `(w* · x) − b ≥ Δ` and `y = −1` if `(w* · x) − b ≤ −Δ`. The label
`y ∈ {1, −1}` is a `Bool`, `true` standing for `1` and `false` for `−1`. A point in the strip
`|(w* · x) − b| < Δ` is classified with neither label. -/
def MarginClassifies {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (b Δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : Bool) : Prop :=
  (y = true → Δ ≤ ⟪w, x⟫_ℝ - b) ∧ (y = false → ⟪w, x⟫_ℝ - b ≤ -Δ)

/-- The vectors `x₁, …, x_h` are **shattered by the Δ-margin separating hyperplanes**: for each of
the `2^h` labelings `y₁, …, y_h ∈ {1, −1}` there is a hyperplane `(w* · x) − b = 0` with
`|w*| = 1` and `b ∈ ℝ` that is a Δ-margin separating hyperplane for every `xᵢ` with its label
`yᵢ` (no point falls in the strip `|(w* · x) − b| < Δ`). Labels are `Bool`
(`true` = `1`, `false` = `−1`); the vectors are indexed by `Fin h`. -/
def MarginShatters {n : ℕ} (Δ : ℝ) {h : ℕ} (x : Fin h → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ y : Fin h → Bool, ∃ (w : EuclideanSpace ℝ (Fin n)) (b : ℝ),
    ‖w‖ = 1 ∧ ∀ i, MarginClassifies w b Δ (x i) (y i)

/-- The **VC dimension of the set of Δ-margin separating hyperplanes** on the set of vectors
`X ⊆ ℝⁿ` (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §5.4.2, p. 132, with the
VC dimension of §3.6, p. 80): the maximum number `h` of vectors `x₁, …, x_h ∈ X` that are shattered
by the Δ-margin separating hyperplanes (`MarginShatters`), and `∞` (`⊤`) if such sets of every
size exist. Valued in `ℕ∞`, where the supremum of an unbounded set of naturals is `⊤` and the
supremum of the empty set is `0`. (For `n = 0` there is no unit vector `w*`, so nothing, not even
the empty family, is shattered and the value is `0`.) -/
noncomputable def marginVCDim {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (Δ : ℝ) : ℕ∞ :=
  ⨆ (h : ℕ) (_ : ∃ x : Fin h → EuclideanSpace ℝ (Fin n), (∀ i, x i ∈ X) ∧ MarginShatters Δ x),
    (h : ℕ∞)

end NatureSLT.Margin


