-- Prove2me | Definitions.Def_GlobalSinkhorn_rowNormalize
-- name    : GlobalSinkhorn_rowNormalize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T04:21:27.730735+00:00
-- url     : https://prove2.me/theorems/2a9ef496-d7c1-42c7-aa4e-80e0f01cf51a
-- title:
--   Row normalization of a matrix
-- statement:
--   For a nonnegative $n\times n$ matrix $M$, **row normalization** divides every entry by the sum of its row:
--   $$
--   \big(\mathcal R(M)\big)_{ij}=\frac{M_{ij}}{\sum_{k}M_{ik}} .
--   $$
--   The result is row-stochastic whenever every row sum is positive. It is one iteration of Sinkhorn–Knopp.
--
--   **Formalization Note** Lean's total division gives $0$ on a zero row. Under the hypotheses of Theorems 1.1 and 3.1 this case never occurs: the row sums met are $(S\mathcal F(w))_i/(Sw)_i>0$ (p.19).
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Section 1, p.3 and Theorem 1.1, p.5

import Mathlib

open Matrix

namespace GlobalSinkhorn

/-- Row normalization: every entry is divided by the sum of its row.
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), p.3 and p.5.

**Formalization Note.** Lean's total division gives `0` on a zero row. Under the hypotheses of
Theorems 1.1 and 3.1 this never fires: the row sums met are `(S F(w)) i / (S w) i > 0` (p.19). -/
noncomputable def rowNormalize {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => M i j / ∑ k, M i k

end GlobalSinkhorn


