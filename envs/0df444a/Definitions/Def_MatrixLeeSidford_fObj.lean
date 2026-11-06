-- Prove2me | Definitions.Def_MatrixLeeSidford_fObj
-- name    : MatrixLeeSidford_fObj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:51.450525+00:00
-- url     : https://prove2.me/theorems/8db57043-70b2-4e97-ae48-acfe77f95a03
-- title:
--   Lewis-weight objective $f(G)=\frac1s\operatorname{tr}[L(G)^s]-\log\det G-m$
-- statement:
--   For an integer $s\ge2$ and an $m\times m$ matrix $G\succ0$, the **objective** of the matrix Lewis-weight potential at the slack $S$ is
--   $$
--   f(G)=\frac1s\operatorname{tr}\big[L(G)^s\big]-\log\det G-m .
--   $$
--   The trace power penalizes the condition $L(G)\preceq I$, and $-\log\det G$ rewards a large ellipsoid $E_G$.
--
--   **Formalization Note** Natural logarithm; the objective is only evaluated at positive definite $G$, where $\det G>0$.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Definition 4.3, Eq. (4.6), p.34; Section 5.1, p.37

import Mathlib
import Definitions.Def_MatrixLeeSidford_Lmap

open Matrix

namespace MatrixLeeSidford

/-- The objective `f(G) := (1/s) tr[L(G)^s] − log det G − m` of the matrix Lewis-weight potential
(Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Definition 4.3, Eq. (4.6), p.34; `f_y = f_{S(y)}`, and `f_S` for a general `S ≻ 0`,
Section 5.1, p.37).

**Formalization Note** `s : ℕ` (the paper's integer `s ≥ 2`; the bound is a hypothesis of each
theorem), natural logarithm `Real.log`. The objective is only meaningful for `G ≻ 0`, where
`det G > 0`. -/
noncomputable def fObj {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) (G : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  (1 / (s : ℝ)) * ((Lmap A S G) ^ s).trace - Real.log G.det - m

end MatrixLeeSidford


