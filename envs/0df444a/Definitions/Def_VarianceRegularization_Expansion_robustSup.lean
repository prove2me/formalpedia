-- Prove2me | Definitions.Def_VarianceRegularization_Expansion_robustSup
-- name    : VarianceRegularization_Expansion_robustSup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:28:47.546054+00:00
-- url     : https://prove2.me/theorems/62188253-580c-4319-b8cd-a41d5e74dc45
-- title:
--   Equation (8): robust sample expectation
-- statement:
--   Given sample values $z=(z_1,\ldots,z_n)$ and the χ² ball $\mathcal P_n(\rho)$ of empirical weights, the **robust expectation** is
--
--   $$R_n(z,\rho)=\sup_{p\in\mathcal P_n(\rho)}\sum_{i=1}^n p_i z_i.$$
--
--   It is the robust-risk value studied in Theorem 1.
--
--   **Formalization Note** The theorems assume $n\ge1$ and $\rho\ge0$, when the feasible set contains uniform weights and the real supremum has its ordinary meaning.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 5, problem (8)

import Mathlib
import Definitions.Def_VarianceRegularization_Expansion_chiSqBall

namespace VarianceRegularization.Expansion

/-- The optimum of (8), the robust expectation of the sample values `z`. For `n > 0` and
`ρ ≥ 0`, uniform weights lie in the ball and the objective image is bounded and compact. -/
noncomputable def robustSup (n : ℕ) (ρ : ℝ) (z : Fin n → ℝ) : ℝ :=
  sSup ((fun p : Fin n → ℝ => ∑ i, p i * z i) '' chiSqBall n ρ)

end VarianceRegularization.Expansion


