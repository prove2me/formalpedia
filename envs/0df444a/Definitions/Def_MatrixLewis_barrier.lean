-- Prove2me | Definitions.Def_MatrixLewis_barrier
-- name    : MatrixLewis_barrier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:09:10.009563+00:00
-- url     : https://prove2.me/theorems/a10c72c4-0a0e-4a56-9e0e-e4ae54a88d7c
-- title:
--   Matrix Lewis barrier $f_q(x)=\varphi_q(S_x)$
-- statement:
--   The **matrix Lewis barrier** of the semidefinite program is
--   $$
--   f_q(x):=\varphi_q(S_x),\qquad x\in\mathcal D .
--   $$
--   On linear programs (diagonal data) it is the Lewis-weight barrier of Lee and Sidford.
--
--   **Formalization Note** A total function on $\mathbb R^m$; outside the open set $\mathcal D$ its values are junk and no statement reads them.
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Definition 3.7, p.19, eq. (9)

import Mathlib
import Definitions.Def_MatrixLewis_slack
import Definitions.Def_MatrixLewis_potential

namespace MatrixLewis

/-- The **matrix Lewis barrier** `f_q(x) := φ_q(S_x)` for `x ∈ 𝒟` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), Definition 3.7,
p.19, eq. (9)).

**Formalization Note** A total function on `ℝᵐ = EuclideanSpace ℝ (Fin m)`; off the open set
`𝒟` its values are junk and no statement reads them (derivatives at `x ∈ 𝒟` only see a
neighbourhood inside `𝒟`). -/
noncomputable def barrier {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  potential q A (slack A C x)

end MatrixLewis


