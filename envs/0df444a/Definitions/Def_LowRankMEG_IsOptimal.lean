-- Prove2me | Definitions.Def_LowRankMEG_IsOptimal
-- name    : LowRankMEG_IsOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:39.498311+00:00
-- url     : https://prove2.me/theorems/4ce3c9d0-5ed6-4d86-a0ed-8ed9cc3ffe4e
-- title:
--   Optimal solutions $X^*\in\mathcal X^*$ of Problem (1)
-- statement:
--   $X^*$ is an **optimal solution** of Problem (1), written $X^*\in\mathcal X^*$, when $X^*\in\mathcal S_n$ and
--   $$
--   f(X^*)\le f(Y)\qquad\text{for all }Y\in\mathcal S_n.
--   $$
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Eq. (1), p.1; 𝒳* at p.3

import Mathlib
import Definitions.Def_PSDPolyApprox_densityMatrices

namespace LowRankMEG

/-- **`X* ∈ 𝒳*`**: `X*` is an optimal solution of Problem (1), `min_{X ∈ 𝒮_n} f(X)`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Eq. (1), p.1; `𝒳*` on p.3. -/
def IsOptimal {n : ℕ} (f : Matrix (Fin n) (Fin n) ℝ → ℝ) (Xs : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Xs ∈ PSDPolyApprox.densityMatrices n ∧ ∀ Y ∈ PSDPolyApprox.densityMatrices n, f Xs ≤ f Y

end LowRankMEG


