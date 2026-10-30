-- Prove2me | Definitions.Def_LevelSetScores_levelSet
-- name    : LevelSetScores_levelSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:36:10.228389+00:00
-- url     : https://prove2.me/theorems/fa49193e-4e42-41d4-a630-f62249c51477
-- title:
--   The $\alpha$ level set $L(g;\alpha)$
-- statement:
--   Let $g : \mathbb R^d \to \mathbb R$ and $\alpha \in \mathbb R$. The **$\alpha$ level set** of $g$ is the upper level set
--   $$L(g;\alpha) := \{ z \in \mathbb R^d : g(z) \ge \alpha \}.$$
--
--   The paper takes $g = f_Y * w$ and constructs scoring functions whose expected value is minimized by $L(f_Y * w;\alpha)$. The inequality is non-strict; the strict set $\{g > \alpha\}$ appears only inside the proof of Theorem 2.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`.
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, §4, display (9), p. 12

import Mathlib

namespace LevelSetScores

/-- **The `α` level set of a function, display (9).**
Meng, Taylor, Ben Taieb, Li, *Scores for Multivariate Distributions and Level Sets*,
arXiv:2002.09578v6, §4, display (9), p. 12: "Let g : Rd → R be a univariate function, and
α ∈ R. We define the α level set of g as L(g;α) := {z ∈ Rd : g(z) ≥ α}."

`levelSet g α` is the upper level set `{z | α ≤ g z}` (non-strict inequality, as in (9)).

**Formalization Note.** `ℝᵈ` is `EuclideanSpace ℝ (Fin d)`. The paper applies (9) to
`g = f_Y ∗ w`; in this mission `g` is a Lebesgue density `Ξ` of the measure `P_Y ∗ w`. -/
def levelSet {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ) (α : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {z | α ≤ g z}

end LevelSetScores


