-- Prove2me | Definitions.Def_MatrixLewis_gram
-- name    : MatrixLewis_gram
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:15.166992+00:00
-- url     : https://prove2.me/theorems/c148b4b0-f4f9-4d28-805b-39f0eb29279e
-- title:
--   Gram map $H_S(Z)_{ij}=\operatorname{tr}(B_iZB_j)$ and its adjoint $H_S^*$
-- statement:
--   At $S\succ0$, with $B_i=B_i(S)$, the **Gram map** $H_S:\mathbb S^n\to\mathbb S^m$ and its trace adjoint $H_S^*:\mathbb S^m\to\mathbb S^n$ are
--   $$
--   H_S(Z)_{ij}:=\operatorname{tr}(B_iZB_j),\qquad H_S^*(M):=\sum_{i,j=1}^m M_{ij}\,\operatorname{sym}(B_iB_j),
--   $$
--   where $\operatorname{sym}(J)=\tfrac12(J+J^\top)$. They satisfy $\langle M,H_S(Z)\rangle=\langle H_S^*(M),Z\rangle$; for $Z\succeq0$, $H_S(Z)$ is the Gram matrix of $B_1Z^{1/2},\dots,B_mZ^{1/2}$ in the Frobenius inner product.
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), §3.1, p.15, eq. (5); sym(J) p.14

import Mathlib
import Definitions.Def_MatrixLewis_scaled

namespace MatrixLewis

/-- The Gram map `H_S : Sⁿ → Sᵐ`, `H_S(Z)ᵢⱼ := tr(Bᵢ Z Bⱼ)` with `Bᵢ = Bᵢ(S)`
(Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), §3.1, p.15, eq. (5)). -/
noncomputable def gram {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S Z : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => (scaled A S i * Z * scaled A S j).trace

/-- `sym(J) := ½(J + Jᵀ)` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), §3.1, p.14). -/
noncomputable def sym {ι : Type*} (J : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (1 / 2 : ℝ) • (J + J.transpose)

/-- The trace adjoint `H*_S : Sᵐ → Sⁿ`, `H*_S(M) := ∑ᵢⱼ Mᵢⱼ sym(BᵢBⱼ)` with `Bᵢ = Bᵢ(S)`
(Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), §3.1, p.15, eq. (5)). -/
noncomputable def gramAdj {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (M : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i, ∑ j, M i j • sym (scaled A S i * scaled A S j)

end MatrixLewis


