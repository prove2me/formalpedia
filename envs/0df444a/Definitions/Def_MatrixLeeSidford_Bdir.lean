-- Prove2me | Definitions.Def_MatrixLeeSidford_Bdir
-- name    : MatrixLeeSidford_Bdir
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:00.871953+00:00
-- url     : https://prove2.me/theorems/24c5422e-00ac-49f9-ae2e-62f905410490
-- title:
--   Directional matrix $B_h=\sum_i h_iB_i$
-- statement:
--   For a direction $h\in\mathbb R^m$, $B_h=\sum_i h_iB_i$, where the $B_i$ are the normalized constraint matrices at the slack $S$. Since $S(y\pm h)=S(y)^{1/2}(I\pm B_h)S(y)^{1/2}$, both $y\pm h$ lie in $\Omega$ iff $\|B_h\|_{op}<1$.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Eq. (4.4), p.32

import Mathlib
import Definitions.Def_MatrixLeeSidford_normB

open Matrix

namespace MatrixLeeSidford

/-- `B_h := ∑ᵢ hᵢ Bᵢ` for a direction `h ∈ ℝᵐ` (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Eq. (4.4), p.32). -/
noncomputable def Bdir {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (h : EuclideanSpace ℝ (Fin m)) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i, h i • normB A S i

end MatrixLeeSidford


