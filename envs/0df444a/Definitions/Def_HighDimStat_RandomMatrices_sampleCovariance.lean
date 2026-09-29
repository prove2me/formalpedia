-- Prove2me | Definitions.Def_HighDimStat_RandomMatrices_sampleCovariance
-- name    : HighDimStat_RandomMatrices_sampleCovariance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:21:01.566986+00:00
-- url     : https://prove2.me/theorems/a6c166a0-02f4-48da-a32a-a09654354596
-- title:
--   The sample covariance matrix
-- statement:
--   The **sample covariance matrix** of a sample $x_1,\dots,x_n\in\mathbb R^d$,
--
--   $$
--   \hat\Sigma \;:=\; \frac1n\sum_{i=1}^n x_ix_i^T.
--   $$
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 179 (PDF p. 199), Corollary 6.20

import Mathlib

namespace HighDimStat.RandomMatrices

/-- The **sample covariance matrix** `Σ̂ := (1/n) ∑ᵢ xᵢxᵢᵀ`, Wainwright, *High-Dimensional
Statistics* (2019), p. 179 (Corollary 6.20) and p. 181 (Theorem 6.23), for a sample
`x₁,...,xₙ ∈ ℝ^d`. -/
noncomputable def sampleCovariance {n d : ℕ} (x : Fin n → Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun j k => (1 / (n : ℝ)) * ∑ i, x i j * x i k

end HighDimStat.RandomMatrices


