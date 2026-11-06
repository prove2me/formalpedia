-- Prove2me | Definitions.Def_MatrixLewis_maximizer
-- name    : MatrixLewis_maximizer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:11:17.422226+00:00
-- url     : https://prove2.me/theorems/19f3c709-b4b3-4b2e-8f9f-420ae68bc8ae
-- title:
--   Maximizer $Z_S=H_S^*(M_*(S))^{p'-1}$
-- statement:
--   The **maximizer** of the matrix Lewis potential at $S\succ0$ is
--   $$
--   Z_S:=H_S^*\bigl(M_*(S)\bigr)^{p'-1}.
--   $$
--   Theorem 3.9(ii) shows it is positive definite and the unique maximizer in the definition of $\varphi_q(S)$.
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Theorem 3.9(ii), p.20

import Mathlib
import Definitions.Def_MatrixLewis_dualMin

namespace MatrixLewis

/-- The maximizer `Z_S := H*_S(M*(S))^{p′−1}` of the matrix Lewis potential (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…),
Theorem 3.9(ii), p.20). -/
noncomputable def maximizer {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  mpow (pDual q - 1) (gramAdj A S (dualMin q A S))

end MatrixLewis


