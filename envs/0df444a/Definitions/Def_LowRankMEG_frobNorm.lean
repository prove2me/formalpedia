-- Prove2me | Definitions.Def_LowRankMEG_frobNorm
-- name    : LowRankMEG_frobNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:21.313907+00:00
-- url     : https://prove2.me/theorems/58e9df9b-8a5e-479d-a687-db8da31bd0e7
-- title:
--   The Frobenius norm $\|A\|_F$
-- statement:
--   The **Frobenius norm** of a real $m\times k$ matrix $A$ is
--   $$
--   \|A\|_F=\Bigl(\sum_{i,j}A_{ij}^2\Bigr)^{1/2}.
--   $$
--   It appears in the Davis–Kahan bound and in the initialization conditions.
--
--   **Formalization Note** It is written out because Mathlib declares no global norm on `Matrix`.
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, §2.1, p.5

import Mathlib

namespace LowRankMEG

/-- **The Frobenius norm** `‖A‖_F` of a real rectangular matrix.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, §2.1, p.5.

**Formalization Note.** Written out, because Mathlib declares no global norm on `Matrix`. -/
noncomputable def frobNorm {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, A i j ^ 2)

end LowRankMEG


