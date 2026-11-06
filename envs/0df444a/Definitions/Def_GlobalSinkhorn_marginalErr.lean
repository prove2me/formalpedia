-- Prove2me | Definitions.Def_GlobalSinkhorn_marginalErr
-- name    : GlobalSinkhorn_marginalErr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T04:21:25.921328+00:00
-- url     : https://prove2.me/theorems/38c5b947-a884-45c0-8d6f-0111b743cede
-- title:
--   Total marginal $\ell_1$ error $\|r(M)-\mathbf 1\|_1+\|c(M)-\mathbf 1\|_1$
-- statement:
--   For an $n\times n$ matrix $M$ with row sums $r_i(M)=\sum_jM_{ij}$ and column sums $c_j(M)=\sum_iM_{ij}$, the **total marginal $\ell_1$ error** is
--   $$
--   \|r(M)-\mathbf 1\|_1+\|c(M)-\mathbf 1\|_1=\sum_{i=1}^n|r_i(M)-1|+\sum_{j=1}^n|c_j(M)-1| .
--   $$
--   A matrix achieves error $\varepsilon$ when this quantity is at most $\varepsilon$; it is $0$ exactly for doubly stochastic row and column sums.
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Eq. (14), p.13 and Theorem 1.1, p.5

import Mathlib

open Matrix

namespace GlobalSinkhorn

/-- The total marginal `ℓ₁` error `‖r(M) − 1‖₁ + ‖c(M) − 1‖₁`.
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), Eq. (14), p.13 and Theorem 1.1, p.5. -/
noncomputable def marginalErr {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, |∑ j, M i j - 1| + ∑ j, |∑ i, M i j - 1|

end GlobalSinkhorn


