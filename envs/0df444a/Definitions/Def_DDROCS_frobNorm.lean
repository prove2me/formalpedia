-- Prove2me | Definitions.Def_DDROCS_frobNorm
-- name    : DDROCS_frobNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:29:59.767169+00:00
-- url     : https://prove2.me/theorems/71245ac2-9540-4775-91d6-31cf8b63c0a0
-- title:
--   Frobenius norm $\|A\|_F$ of a square matrix
-- statement:
--   For a real $d\times d$ matrix $A$, the **Frobenius norm** is
--
--   $$
--   \|A\|_F \;=\; \Bigl(\sum_{i=1}^d \sum_{j=1}^d A_{ij}^2\Bigr)^{1/2}.
--   $$
--
--   It measures the distance between a candidate covariance and the sample covariance in the confidence region $\mathcal P^{CS}$.
--
--   **Formalization Note** Defined explicitly; Mathlib's default norm on matrices is the entrywise sup norm, which is a different quantity.
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Sec. 8.1, p. 24

import Mathlib

namespace DDROCS

/-- **Frobenius norm of a square matrix**, `‖A‖_F`.
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Sec. 8.1, p. 24:
"Let `‖·‖_F` denote the Frobenius norm of matrices."

`frobNorm A = √(Σ_i Σ_j A_ij²)`.

**Formalization Note.** Defined explicitly so that it cannot be confused with Mathlib's default
norm on `Matrix`, which is the entrywise sup norm. -/
noncomputable def frobNorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, A i j ^ 2)

end DDROCS


