-- Prove2me | Definitions.Def_GlobalSinkhorn_skIter
-- name    : GlobalSinkhorn_skIter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T04:22:38.99995+00:00
-- url     : https://prove2.me/theorems/67fc7493-faa4-46e3-9d8e-af0bc013e4b3
-- title:
--   The Sinkhorn–Knopp iterates $A^{(k)}$
-- statement:
--   Starting from $A^{(0)}=A$, the **Sinkhorn–Knopp iteration** alternately normalizes columns and rows, a column step first:
--   $$
--   A^{(2t+1)}=\mathcal C\big(A^{(2t)}\big),\qquad A^{(2t+2)}=\mathcal R\big(A^{(2t+1)}\big),\qquad t\ge0,
--   $$
--   where $\mathcal C$ and $\mathcal R$ are column and row normalization. One normalization counts as one iteration, so $A^{(2t)}$ is the matrix after $t$ complete column–row cycles. Since the input is row-stochastic, the first step that changes anything is a column step.
--
--   **Formalization Note** `skIter A k` is $A^{(k)}$; step $k+1$ is a column normalization when $k$ is even and a row normalization when $k$ is odd. The normalizations use Lean's total division (see `colNormalize`, `rowNormalize`).
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Section 1, p.3 and Theorem 1.1, p.5

import Mathlib
import Definitions.Def_GlobalSinkhorn_colNormalize
import Definitions.Def_GlobalSinkhorn_rowNormalize

open Matrix

namespace GlobalSinkhorn

/-- The Sinkhorn–Knopp iterates `A⁽ᵏ⁾`: `A⁽⁰⁾ = A`, followed by alternating column and row
normalizations, a column step first. He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), p.3 and Theorem 1.1, p.5.

**Formalization Note.** One normalization is one iteration, so `skIter A (2 * t)` is `A⁽²ᵗ⁾`,
the matrix after `t` complete column–row cycles. -/
noncomputable def skIter {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => A
  | k + 1 => if Even k then colNormalize (skIter A k) else rowNormalize (skIter A k)

end GlobalSinkhorn


