-- Prove2me | Definitions.Def_LowRankMEG_IsCompactEigen
-- name    : LowRankMEG_IsCompactEigen
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:22.627984+00:00
-- url     : https://prove2.me/theorems/655a15de-2ea7-4356-b428-1e46ad542588
-- title:
--   Compact-form eigen-decomposition
-- statement:
--   A **compact-form eigen-decomposition** of a rank-$r$ matrix $M$ is $M=V_r\Lambda_rV_r^\top$, where $V_r\in\mathbb R^{n\times r}$ has orthonormal columns, the eigenvectors associated with nonzero eigenvalues, and $\Lambda_r\succ0$ is the diagonal matrix of these eigenvalues.
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Lemma 4 and footnote 6, p.17

import Mathlib
open Matrix

namespace LowRankMEG

/-- **A compact-form eigen-decomposition** `M = V_r Λ_r V_rᵀ` of a rank-`r` matrix: `V_r ∈ ℝ^{n×r}` with
orthonormal columns and `Λ_r` the diagonal matrix of the nonzero eigenvalues of `M`, here positive.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Lemma 4 and its footnote 6, p.17. -/
def IsCompactEigen {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (V : Matrix (Fin n) (Fin M.rank) ℝ)
    (Λ : Fin M.rank → ℝ) : Prop :=
  Vᵀ * V = 1 ∧ (∀ i, 0 < Λ i) ∧ M = V * diagonal Λ * Vᵀ

end LowRankMEG


