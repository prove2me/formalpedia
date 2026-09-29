-- Prove2me | Definitions.Def_HighDimStat_RandomMatrices_opNorm
-- name    : HighDimStat_RandomMatrices_opNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:19:02.410712+00:00
-- url     : https://prove2.me/theorems/b70418ff-f036-4722-af49-3ad903d9e087
-- title:
--   The operator (spectral) norm of a matrix
-- statement:
--   The **operator (spectral) norm** $|\!|\!|M|\!|\!|_2$, the largest singular value of $M$, used
--   throughout Chapter 6 to measure the size of a random matrix's deviation from its mean.
--
--   **Formalization Note** Realized as the operator norm of the continuous linear endomorphism of
--   Euclidean space that $M$ induces (`Matrix.toEuclideanCLM`).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, Chapter 6, notation |||.|||_2

import Mathlib

namespace HighDimStat.RandomMatrices

/-- The **operator (spectral) norm** `|||M|||₂`, Wainwright, *High-Dimensional Statistics* (2019),
used throughout Chapter 6. Realized as the operator norm of the continuous linear endomorphism of
Euclidean space that `M` induces (`Matrix.toEuclideanCLM`), i.e. the largest singular value of
`M`. -/
noncomputable def opNorm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖

end HighDimStat.RandomMatrices


