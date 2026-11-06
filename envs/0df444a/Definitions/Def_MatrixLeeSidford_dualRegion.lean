-- Prove2me | Definitions.Def_MatrixLeeSidford_dualRegion
-- name    : MatrixLeeSidford_dualRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:02.887007+00:00
-- url     : https://prove2.me/theorems/f955237d-97db-417a-8980-459afb4b73e8
-- title:
--   Strictly feasible dual region $\Omega=\{y: S(y)\succ0\}$
-- statement:
--   The **strictly feasible dual region** of the pencil is
--   $$
--   \Omega=\{y\in\mathbb R^m : S(y)\succ0\},
--   $$
--   the set of dual points whose slack is positive definite. It is open and convex; the matrix Lee–Sidford barrier is a self-concordant barrier for $\Omega$.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), p.29 and Eq. (4.3), p.32

import Mathlib
import Definitions.Def_MatrixLeeSidford_slack

open Matrix

namespace MatrixLeeSidford

/-- The strictly feasible dual region `Ω := {y ∈ ℝᵐ : S(y) ≻ 0}` (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), p.29 and
Eq. (4.3), p.32).

**Formalization Note** `Matrix.PosDef` includes symmetry of `S(y)`. -/
def dualRegion {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {y | (slack A C y).PosDef}

end MatrixLeeSidford


