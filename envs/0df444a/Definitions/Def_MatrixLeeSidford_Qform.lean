-- Prove2me | Definitions.Def_MatrixLeeSidford_Qform
-- name    : MatrixLeeSidford_Qform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:36:55.059002+00:00
-- url     : https://prove2.me/theorems/be236c66-584d-4175-8459-cf4e3affaf88
-- title:
--   Proxy Hessian $Q[h,h]=\operatorname{tr}[MB_h^2]$
-- statement:
--   The **proxy Hessian** at the slack $S$ is the quadratic form $Q[h,h]=\operatorname{tr}[MB_h^2]$ on $\mathbb R^m$, with $M$ the gradient matrix. It approximates the Hessian of $\Phi_p$ within the factor $2s+1$ (Lemma 5.6).
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Definition 5.5, Eq. (5.15), p.42; Theorem 2.1(c), p.29

import Mathlib
import Definitions.Def_MatrixLeeSidford_Mmat
import Definitions.Def_MatrixLeeSidford_Bdir

open Matrix

namespace MatrixLeeSidford

/-- The proxy Hessian `Q[h, h] := tr[M B_h²]` (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Definition 5.5, Eq. (5.15), p.42;
Theorem 2.1(c), p.29). -/
noncomputable def Qform {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) (h : EuclideanSpace ℝ (Fin m)) : ℝ :=
  (Mmat A S s * (Bdir A S h) ^ 2).trace

end MatrixLeeSidford


