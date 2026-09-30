-- Prove2me | Definitions.Def_SteuerChoo_Lexico_lamBar
-- name    : SteuerChoo_Lexico_lamBar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:50:25.083988+00:00
-- url     : https://prove2.me/theorems/53e4db96-59c8-4a6b-b132-48b42e104346
-- title:
--   The weights $\bar\lambda$ of eq. (4.3)
-- statement:
--   Let $z^*$ be the ideal criterion vector and $\bar z\in\mathbb R^k$. The weight vector $\bar\lambda$ of eq. (4.3) is
--   $$
--   \bar\lambda_i=\begin{cases}
--   \dfrac{1}{z^*_i-\bar z_i}\Big[\displaystyle\sum_{j=1}^k\frac{1}{z^*_j-\bar z_j}\Big]^{-1} & \text{if } \bar z_j\ne z^*_j \text{ for all } j,\\[2mm]
--   1 & \text{if } \bar z_i=z^*_i,\\[1mm]
--   0 & \text{if } \bar z_i\ne z^*_i \text{ but } \bar z_j=z^*_j \text{ for some } j.
--   \end{cases}
--   $$
--   In the first case the weights are inversely proportional to the gaps $z^*_i-\bar z_i$, so that all the products $\bar\lambda_i(z^*_i-\bar z_i)$ are equal; in the other cases the weight is concentrated on the coordinates where $\bar z$ touches $z^*$.
--
--   These are the weights under which a given nondominated vector $\bar z$ is the unique solution of the lexicographic weighted Tchebycheff program (Theorem 4.5).
--
--   **Formalization Note** The first case divides only when every $z^*_j-\bar z_j$ is nonzero. The definition does not by itself assert $\bar\lambda\in\bar\Lambda$: that holds for $\bar z\in N$ with $z^*$ an ideal vector (at most one coordinate of such $\bar z$ can equal $z^*_j$), and is part of the conclusion of Theorem 4.5, not an assumption.
-- source:
--   Steuer and Choo, An Interactive Weighted Tchebycheff Procedure for Multiple Objective Programming, Math. Programming 26 (1983), p. 334, eq. (4.3)

import Mathlib

namespace SteuerChoo.Lexico

/-- The weights `λ̄` of eq. (4.3), p. 334:
`λ̄_i = [1/(z*_i − z̄_i)] [Σ_j 1/(z*_j − z̄_j)]⁻¹` if `z̄_j ≠ z*_j` for all `j`;
`λ̄_i = 1` if `z̄_i = z*_i`; `λ̄_i = 0` if `z̄_i ≠ z*_i` but `z̄_j = z*_j` for some `j`. -/
noncomputable def lamBar {k : ℕ} (zstar zbar : Fin k → ℝ) : Fin k → ℝ := fun i =>
  if ∀ j, zbar j ≠ zstar j then
    (1 / (zstar i - zbar i)) * (∑ j, 1 / (zstar j - zbar j))⁻¹
  else if zbar i = zstar i then 1 else 0

end SteuerChoo.Lexico


