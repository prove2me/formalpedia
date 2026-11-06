-- Prove2me | Definitions.Def_GlobalSinkhorn_colNormalize
-- name    : GlobalSinkhorn_colNormalize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T04:21:25.06296+00:00
-- url     : https://prove2.me/theorems/c29f7117-a1b6-4831-b5a6-0f85f9b2ae49
-- title:
--   Column normalization of a matrix
-- statement:
--   For a nonnegative $n\times n$ matrix $M$, **column normalization** divides every entry by the sum of its column:
--   $$
--   \big(\mathcal C(M)\big)_{ij}=\frac{M_{ij}}{\sum_{k}M_{kj}} .
--   $$
--   The result is column-stochastic whenever every column sum is positive. It is one iteration of Sinkhorn–Knopp.
--
--   **Formalization Note** Lean's total division gives $0$ on a zero column. Under the hypotheses of Theorems 1.1 and 3.1 this case never occurs: every iterate is $M(w)$, whose column sums $w_j/\mathcal F(w)_j$ are positive (p.19).
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Section 1, p.3 and Theorem 1.1, p.5

import Mathlib

open Matrix

namespace GlobalSinkhorn

/-- Column normalization: every entry is divided by the sum of its column.
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), p.3 and p.5.

**Formalization Note.** Lean's total division gives `0` on a zero column. Under the hypotheses
of Theorems 1.1 and 3.1 this never fires: the iterates are `M(w)`, whose column sums
`w j / F(w) j` are positive (p.19). -/
noncomputable def colNormalize {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => M i j / ∑ k, M k j

end GlobalSinkhorn


