-- Prove2me | Definitions.Def_MatrixLeeSidford_Mmat
-- name    : MatrixLeeSidford_Mmat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:35:58.817505+00:00
-- url     : https://prove2.me/theorems/5eeed78b-754f-4a4b-8bd6-46c99d481564
-- title:
--   Gradient matrix $M$
-- statement:
--   At the slack $S$, with optimal weight $G_*$ and $W=L(G_*)^{s-1}$, the **gradient matrix** is
--   $$
--   M=\frac12\Big(L(G_*)^s+\sum_{i,j}(G_*)_{ij}\,B_iWB_j\Big).
--   $$
--   It gives the gradient of the potential, $\nabla\Phi_p(y)[h]=-\operatorname{tr}[M_yB_h]$ (Lemma 5.6), and the proxy Hessian.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Definition 5.5, Eq. (5.15), p.42; Theorem 2.1(c), p.29

import Mathlib
import Definitions.Def_MatrixLeeSidford_Wmat

open Matrix

namespace MatrixLeeSidford

/-- The gradient matrix `M := ½ (L(G_*)^s + ∑_{i,j} (G_*)ᵢⱼ Bᵢ W Bⱼ)` (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Definition 5.5,
Eq. (5.15), p.42; Theorem 2.1(c), p.29). -/
noncomputable def Mmat {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • ((Lmap A S (optWeight A S s)) ^ s +
    ∑ i, ∑ j, optWeight A S s i j • (normB A S i * Wmat A S s * normB A S j))

end MatrixLeeSidford


