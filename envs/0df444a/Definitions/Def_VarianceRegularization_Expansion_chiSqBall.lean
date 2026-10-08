-- Prove2me | Definitions.Def_VarianceRegularization_Expansion_chiSqBall
-- name    : VarianceRegularization_Expansion_chiSqBall
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:15:12.732978+00:00
-- url     : https://prove2.me/theorems/47a8fe83-adf1-40a4-88b6-db57d4f0a3e5
-- title:
--   Equation (8): the χ² ball of empirical weights
-- statement:
--   For a sample of size $n$, the **χ² ball** of radius $\rho$ consists of nonnegative weights $p_1,\ldots,p_n$ satisfying
--
--   $$\sum_{i=1}^n p_i=1,\qquad \frac12\sum_{i=1}^n(np_i-1)^2\le\rho.$$
--
--   This is the feasible set of the paper's finite robust optimization problem (8).
--
--   **Formalization Note** The weights are indexed by `Fin n`. The paper's distributional ball around the empirical distribution has the same robust-risk supremum, including when observations repeat: mass at tied observations can be split evenly among their indices.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 5, eq. (8); p. 2, eq. (4)

import Mathlib

namespace VarianceRegularization.Expansion

/-- Equation (8), p. 5: the chi-square ball of sample weights. A weight vector describes a
distribution supported on the empirical sample. If sample values tie, splitting mass equally
among equal observations recovers the same supremum as the distribution formulation (4). -/
def chiSqBall (n : ℕ) (ρ : ℝ) : Set (Fin n → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
    (1 / 2 : ℝ) * ∑ i, ((n : ℝ) * p i - 1) ^ 2 ≤ ρ}

end VarianceRegularization.Expansion


