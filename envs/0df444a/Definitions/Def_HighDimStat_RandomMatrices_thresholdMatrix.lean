-- Prove2me | Definitions.Def_HighDimStat_RandomMatrices_thresholdMatrix
-- name    : HighDimStat_RandomMatrices_thresholdMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:19:59.162987+00:00
-- url     : https://prove2.me/theorems/3b092517-43c7-4d05-95cd-07f78f3fd1a5
-- title:
--   The hard-thresholding operator, applied entrywise to a matrix
-- statement:
--   **Eq. (6.52).** The scalar hard-thresholding operator
--
--   $$
--   T_\lambda(u) \;:=\; u\cdot\mathbb 1[|u|>\lambda],
--   $$
--
--   extended entrywise to a matrix $M$: $T_\lambda(M)_{ij} := T_\lambda(M_{ij})$. This is the
--   thresholding estimator $T_{\lambda_n}(\hat\Sigma)$ studied by Theorem 6.23.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 180 (PDF p. 200), Eq. (6.52)

import Mathlib

namespace HighDimStat.RandomMatrices

/-- **Eq. (6.52)** (hard-thresholding operator), Wainwright, *High-Dimensional Statistics*
(2019), p. 180. The scalar hard-thresholding operator `Tλ(u) := u·I[|u|>λ]`, extended entrywise
to a matrix `M`: `Tλ(M)_{ij} := Tλ(M_{ij})`. -/
noncomputable def thresholdMatrix {d : ℕ} (lam : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => if lam < |M i j| then M i j else 0

end HighDimStat.RandomMatrices


