-- Prove2me | Definitions.Def_SimplexProj_Condat_IsL1Projection
-- name    : SimplexProj_Condat_IsL1Projection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T23:02:30.46658+00:00
-- url     : https://prove2.me/theorems/86b76d97-b131-4b1f-b3a7-cbfffcb8d020
-- title:
--   $x$ is the Euclidean projection $P_B(y)$ of $y$ onto the $\ell_1$ ball (Eq. (2))
-- statement:
--   Let $B \subset \mathbb{R}^N$ be the $\ell_1$ ball of radius $a$ (vectors whose absolute values sum to at most $a$). For $y, x \in \mathbb{R}^N$, we say that **$x$ is a Euclidean projection of $y$ onto $B$** if $x \in B$ and $x$ minimizes the Euclidean distance to $y$ over $B$:
--
--   $$x \in B \quad\text{and}\quad \sum_{n=1}^N (x_n - y_n)^2 \le \sum_{n=1}^N (z_n - y_n)^2 \ \text{ for every } z \in B.$$
--
--   This is the relation $x = P_B(y) := \operatorname{argmin}_{x \in B} \|x - y\|$ of Condat, Eq. (2), with $\|\cdot\|$ the Euclidean norm.
--
--   **Formalization Note.** As for the simplex, the projection is a predicate and the squared Euclidean distance is an explicit sum of squares (not Mathlib's sup norm on `Fin N → ℝ`).
-- source:
--   Condat, Fast Projection onto the Simplex and the ℓ1 Ball, HAL hal-01056171v2, p. 1, Eq. (2)

import Mathlib
import Definitions.Def_SimplexProj_Condat_l1Ball

namespace SimplexProj.Condat

/-- `x` is a Euclidean projection of `y` onto the `ℓ1` ball `B` of radius `a` (Condat, Eq. (2)):
`x ∈ B` and `x` minimizes the Euclidean distance `‖z - y‖` (equivalently its square
`∑ n, (z n - y n) ^ 2`) over `z ∈ B`. -/
def IsL1Projection {N : ℕ} (a : ℝ) (y x : Fin N → ℝ) : Prop :=
  x ∈ l1Ball a ∧ ∀ z ∈ l1Ball a, ∑ n, (x n - y n) ^ 2 ≤ ∑ n, (z n - y n) ^ 2

end SimplexProj.Condat


