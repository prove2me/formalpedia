-- Prove2me | Definitions.Def_MatrixLewis_gapDelta
-- name    : MatrixLewis_gapDelta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:08:37.429064+00:00
-- url     : https://prove2.me/theorems/30ccb24b-33fe-4d95-8db2-799190be80d8
-- title:
--   Primal point, gap matrix $\Psi$ and gap $\Delta(M)$
-- statement:
--   A dual point $M\succ0$ determines
--   $$
--   A:=H_S^*(M),\quad Z:=A^{p'-1},\quad H_Z:=H_S(Z),\quad \Psi:=M^{1/2}H_ZM^{1/2},
--   $$
--   and the **gap**
--   $$
--   \Delta(M):=\operatorname{tr}\Psi-\log\det\Psi-m .
--   $$
--   Also $\varrho(t):=t-\log t-1$ for $t>0$, so $\Delta(M)$ is the sum of $\varrho$ over the eigenvalues of $\Psi$.
--
--   **Formalization Note** `primalOf` is $Z=A^{p'-1}$, `gapMatrix` is $\Psi$, `gapDelta` is $\Delta$, `rho` is $\varrho$.
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Definition 3.7, p.19, eqs. (13)–(14)

import Mathlib
import Definitions.Def_MatrixLewis_gram
import Definitions.Def_MatrixLewis_pExp

namespace MatrixLewis

/-- `ϱ(t) := t − log t − 1` for `t > 0` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), Definition 3.7, p.19). -/
noncomputable def rho (t : ℝ) : ℝ := t - Real.log t - 1

/-- The primal point `Z := A^{p′−1}` determined by a dual point `M`, where `A := H*_S(M)`
(Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), Definition 3.7, p.19, eq. (13)). -/
noncomputable def primalOf {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (M : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  mpow (pDual q - 1) (gramAdj A S M)

/-- The gap matrix `Ψ := M^{1/2} H_Z M^{1/2}` with `H_Z := H_S(Z)`, `Z = (H*_S(M))^{p′−1}`
(Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), Definition 3.7, p.19, eq. (13)). -/
noncomputable def gapMatrix {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (M : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  mpow (1 / 2 : ℝ) M * gram A S (primalOf q A S M) * mpow (1 / 2 : ℝ) M

/-- The gap `Δ(M) := tr Ψ − log det Ψ − m` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), Definition 3.7, p.19, eq. (14)). -/
noncomputable def gapDelta {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (M : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  (gapMatrix q A S M).trace - Real.log (gapMatrix q A S M).det - m

end MatrixLewis


