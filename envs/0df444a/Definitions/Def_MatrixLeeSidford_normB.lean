-- Prove2me | Definitions.Def_MatrixLeeSidford_normB
-- name    : MatrixLeeSidford_normB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:17.263057+00:00
-- url     : https://prove2.me/theorems/225e168a-3868-4de4-b1a8-4b1e293e927d
-- title:
--   Normalized constraint matrices $B_i=S^{-1/2}A_iS^{-1/2}$
-- statement:
--   At a positive definite slack matrix $S$ (for instance $S=S(y)$ with $y\in\Omega$) the **normalized constraint matrices** are
--   $$
--   B_i=S^{-1/2}A_iS^{-1/2},\qquad i=1,\dots,m,
--   $$
--   where $S^{-1/2}$ is the inverse of the positive square root of $S$. Section 5.1 uses the same matrices at an arbitrary $S\succ0$.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Eq. (4.4), p.32; Section 5.1, p.37

import Mathlib
import Definitions.Def_MatrixLeeSidford_matRpow

open Matrix

namespace MatrixLeeSidford

/-- The normalized constraint matrices `Bᵢ := S^{-1/2} Aᵢ S^{-1/2}` at a slack matrix `S ≻ 0`
(Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Eq. (4.4), p.32, with `S = S(y)`; for a general `S ≻ 0` as in Section 5.1, p.37).

**Formalization Note** `S^{-1/2}` is `matRpow (-1/2) S`, the inverse of the positive square root
when `S` is positive definite. At `S = S(y)` write `normB A (slack A C y) i`. -/
noncomputable def normB {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (i : Fin m) : Matrix (Fin n) (Fin n) ℝ :=
  matRpow (-(1 / 2)) S * A i * matRpow (-(1 / 2)) S

end MatrixLeeSidford


