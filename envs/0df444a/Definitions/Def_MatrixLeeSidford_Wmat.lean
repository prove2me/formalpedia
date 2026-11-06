-- Prove2me | Definitions.Def_MatrixLeeSidford_Wmat
-- name    : MatrixLeeSidford_Wmat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:20.480024+00:00
-- url     : https://prove2.me/theorems/a81d27c5-613a-49b8-b170-3af7582b27d5
-- title:
--   Dual weight $W=L(G_*)^{s-1}$
-- statement:
--   At the slack $S$, $W=L(G_*)^{s-1}$, where $G_*$ is the optimal weight. Stationarity of $G_*$ reads $L^*(W)=G_*^{-1}$, and $W$ is the maximizer of the dual formulation (4.9).
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Eq. (4.7), p.34; Theorem 2.1(c), p.29

import Mathlib
import Definitions.Def_MatrixLeeSidford_Lmap
import Definitions.Def_MatrixLeeSidford_optWeight

open Matrix

namespace MatrixLeeSidford

/-- `W := L(G_*)^{s−1}` (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Eq. (4.7), p.34; Theorem 2.1(c), p.29). -/
noncomputable def Wmat {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (Lmap A S (optWeight A S s)) ^ (s - 1)

end MatrixLeeSidford


