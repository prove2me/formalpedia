-- Prove2me | Definitions.Def_MatrixLewis_Fdu
-- name    : MatrixLewis_Fdu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:08:44.707976+00:00
-- url     : https://prove2.me/theorems/65974eea-be42-4b77-9414-4e0c4d2b73d4
-- title:
--   Dual objective $F_{\mathrm{du}}(M)$ and $\mathcal J(S,M)=\frac12F^S_{\mathrm{du}}(M)$
-- statement:
--   For $M\in\mathbb S^m_{++}$, the **dual objective** is
--   $$
--   F_{\mathrm{du}}(M):=-\log\det M+\frac1{p'}\operatorname{tr}\bigl(H_S^*(M)^{p'}\bigr)-m,
--   $$
--   written $F^S_{\mathrm{du}}$ when the slack varies, and
--   $$
--   \mathcal J(S,M):=\tfrac12F^S_{\mathrm{du}}(M)\qquad(S\in\mathbb S^n_{++},\ M\in\mathbb S^m_{++}).
--   $$
--   Theorem 3.9 shows $\varphi_q(S)=\min_{M\succ0}\mathcal J(S,M)$.
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Definition 3.7, p.19, eqs. (11)–(12)

import Mathlib
import Definitions.Def_MatrixLewis_gram
import Definitions.Def_MatrixLewis_pExp

namespace MatrixLewis

/-- The dual objective `F_du(M) := −log det M + (1/p′) tr(H*_S(M)^{p′}) − m` for `M ∈ Sᵐ₊₊`
(Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), Definition 3.7, p.19, eq. (11)); written `F^S_du` when the slack varies.
Only read at positive definite `M`. -/
noncomputable def Fdu {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (M : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  -Real.log M.det + (1 / pDual q) * (mpow (pDual q) (gramAdj A S M)).trace - m

/-- `𝒥(S, M) := ½ F^S_du(M)` for `S ∈ Sⁿ₊₊`, `M ∈ Sᵐ₊₊` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), Definition 3.7, p.19,
eq. (12)), also called the dual objective. -/
noncomputable def Jdual {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (M : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  (1 / 2 : ℝ) * Fdu q A S M

end MatrixLewis


