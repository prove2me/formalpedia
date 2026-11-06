-- Prove2me | Definitions.Def_MatrixLeeSidford_optWeightAt
-- name    : MatrixLeeSidford_optWeightAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:48.699401+00:00
-- url     : https://prove2.me/theorems/495a9558-8d43-4f54-9f66-542c9bc7ef66
-- title:
--   Optimal weight at a dual point, $G_*(y)$
-- statement:
--   For $y\in\Omega$, $G_*(y)=G_*(S(y))$, the minimizer of $f_y$ over $G\succ0$; it is the matrix whose ellipsoid $m^{-1/(2s)}E_{G_*(y)}$ is inscribed in the symmetrized local region (Corollary 4.5).
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Theorem 2.1(a), p.29; Lemma 4.4, p.34

import Mathlib
import Definitions.Def_MatrixLeeSidford_optWeight
import Definitions.Def_MatrixLeeSidford_slack

open Matrix

namespace MatrixLeeSidford

/-- The optimal weight at a dual point, `G_*(y) := G_*(S(y))` (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Theorem 2.1(a), p.29;
Lemma 4.4, p.34). -/
noncomputable def optWeightAt {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) (y : EuclideanSpace ℝ (Fin m)) :
    Matrix (Fin m) (Fin m) ℝ :=
  optWeight A (slack A C y) s

end MatrixLeeSidford


