-- Prove2me | Definitions.Def_SimplexProj_Condat_IsSimplexProjection
-- name    : SimplexProj_Condat_IsSimplexProjection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T22:53:52.136999+00:00
-- url     : https://prove2.me/theorems/9b0e8003-d8bd-4d30-920e-ac9156133680
-- title:
--   $x$ is the Euclidean projection $P_\Delta(y)$ of $y$ onto the simplex (Eq. (1))
-- statement:
--   Let $\Delta \subset \mathbb{R}^N$ be the simplex of radius $a$ (nonnegative vectors with entries summing to $a$). For $y, x \in \mathbb{R}^N$, we say that **$x$ is a Euclidean projection of $y$ onto $\Delta$** if $x \in \Delta$ and $x$ minimizes the Euclidean distance to $y$ over $\Delta$:
--
--   $$x \in \Delta \quad\text{and}\quad \sum_{n=1}^N (x_n - y_n)^2 \le \sum_{n=1}^N (z_n - y_n)^2 \ \text{ for every } z \in \Delta.$$
--
--   This is the relation $x = P_\Delta(y) := \operatorname{argmin}_{x \in \Delta} \|x - y\|$ of Condat, Eq. (1), with $\|\cdot\|$ the Euclidean norm; minimizing the squared distance is equivalent to minimizing the distance. The projection exists and is unique (Condat, p. 2), so the predicate pins $x$ down.
--
--   **Formalization Note.** The projection is written as a predicate rather than through a choice of minimizer. The squared Euclidean distance is spelled out as a finite sum of squares; Mathlib's norm on `Fin N → ℝ` (the sup norm) is not used.
-- source:
--   Condat, Fast Projection onto the Simplex and the ℓ1 Ball, HAL hal-01056171v2, p. 1, Eq. (1)

import Mathlib
import Definitions.Def_SimplexProj_Condat_scaledSimplex

namespace SimplexProj.Condat

/-- `x` is a Euclidean projection of `y` onto the simplex `Δ` of radius `a` (Condat, Eq. (1)):
`x ∈ Δ` and `x` minimizes the Euclidean distance `‖z - y‖` (equivalently its square
`∑ n, (z n - y n) ^ 2`) over `z ∈ Δ`. -/
def IsSimplexProjection {N : ℕ} (a : ℝ) (y x : Fin N → ℝ) : Prop :=
  x ∈ scaledSimplex a ∧ ∀ z ∈ scaledSimplex a, ∑ n, (x n - y n) ^ 2 ≤ ∑ n, (z n - y n) ^ 2

end SimplexProj.Condat


