-- Prove2me | Definitions.Def_MatrixLeeSidford_Ladj
-- name    : MatrixLeeSidford_Ladj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:00.681418+00:00
-- url     : https://prove2.me/theorems/b79b563f-2531-419b-88e8-893f2d78eaf5
-- title:
--   Adjoint map $L^*(W)$
-- statement:
--   The adjoint of $L$ with respect to the trace inner product sends an $n\times n$ matrix $W$ to the $m\times m$ matrix
--   $$
--   \big(L^*(W)\big)_{ij}=\tfrac12\operatorname{tr}\big[W(B_iB_j+B_jB_i)\big],
--   $$
--   so that $h^\top L^*(W)h=\operatorname{tr}[WB_h^2]$.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Definition 4.3, p.34

import Mathlib
import Definitions.Def_MatrixLeeSidford_normB

open Matrix

namespace MatrixLeeSidford

/-- The adjoint `L^*` of `L` for the trace inner product, `(L^*(W))ᵢⱼ := ½ tr[W(BᵢBⱼ + BⱼBᵢ)]`
(Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Definition 4.3, p.34). -/
noncomputable def Ladj {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (W : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j =>
    (1 / 2 : ℝ) * (W * (normB A S i * normB A S j + normB A S j * normB A S i)).trace

end MatrixLeeSidford


