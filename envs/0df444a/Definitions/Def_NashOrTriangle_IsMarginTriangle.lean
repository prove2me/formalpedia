-- Prove2me | Definitions.Def_NashOrTriangle_IsMarginTriangle
-- name    : NashOrTriangle_IsMarginTriangle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:34.857929+00:00
-- url     : https://prove2.me/theorems/1b7956cc-cd40-4ebc-ba83-32663bf89f63
-- title:
--   $(t,\gamma)$-triangle (triangle with margin $\gamma$)
-- statement:
--   A **$(t, \gamma)$-triangle** is a sub-game on distinct rows $a_1, \dots, a_t$ and distinct columns $b_1, \dots, b_t$ such that for some threshold $\theta$
--   $$
--   M(a_i, b_j) \ge \theta + \gamma \quad (i \le j), \qquad M(a_i, b_j) \le \theta \quad (i > j).
--   $$
--   This is the real-valued analogue of a $t$-triangle, used in Theorem 2.1(b) with $\gamma = c/k$; in a binary game a triangle of positive margin with $t \ge 2$ is an ordinary $t$-triangle.
--
--   **Formalization Note** "Sub-game" is read as $t$ distinct rows and $t$ distinct columns. $\theta$ is real. Both inequalities are non-strict and the diagonal is on the $\ge \theta + \gamma$ side, as in display (1).
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), §1.1, p.3 (PDF p.4), display (1)

import Mathlib

namespace NashOrTriangle

/-- A **`(t, γ)`-triangle** (a triangle with margin `γ`): distinct rows `a₁, …, a_t`, distinct
columns `b₁, …, b_t` and a threshold `θ` with
`M(aᵢ, bⱼ) ≥ θ + γ` for `i ≤ j` and `M(aᵢ, bⱼ) ≤ θ` for `i > j`.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), §1.1, printed p. 3 (PDF p. 4), display (1): "a (t, γ)-triangle is a sub-game such that
for some θ: M(ai, bj) ≥ θ + γ (i ≤ j), M(ai, bj) ≤ θ (i > j)."

**Formalization Note** "Sub-game" is read as `t` distinct rows and `t` distinct columns
(injectivity), as for `t`-triangles; for `γ > 0` and `t ≥ 2` distinctness follows from (1)
anyway. `θ` is real (a rational `θ`, as in the paper's search, gives the same family). Both
inequalities of (1) are non-strict and the diagonal is on the `≥ θ + γ` side. -/
def IsMarginTriangle {A B : Type*} (M : A → B → ℚ) (γ : ℝ) {t : ℕ} (a : Fin t → A)
    (b : Fin t → B) : Prop :=
  Function.Injective a ∧ Function.Injective b ∧
    ∃ θ : ℝ, ∀ i j, (i ≤ j → θ + γ ≤ (M (a i) (b j) : ℝ)) ∧ (j < i → (M (a i) (b j) : ℝ) ≤ θ)

end NashOrTriangle


