-- Prove2me | Definitions.Def_MatrixLewis_lewisWeight
-- name    : MatrixLewis_lewisWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:12:36.315775+00:00
-- url     : https://prove2.me/theorems/f852d0ae-1fe1-414d-bd29-7aeb2a617264
-- title:
--   Right weight $W_S$, left weight $\Gamma_S$ and matrix Lewis weight $\Lambda_S$
-- statement:
--   At $S\succ0$, with $B_i=B_i(S)$, maximizer $Z_S$ and dual minimizer $M_*=M_*(S)$, the **right weight**, **left weight** and **matrix Lewis weight** are
--   $$
--   W_S:=Z_S^p,\qquad \Gamma_S:=\sum_{i,j=1}^m(M_*)_{ij}\,B_iZ_SB_j,\qquad \Lambda_S:=\tfrac12(W_S+\Gamma_S).
--   $$
--   (The paper notes $W_S=H_S^*(M_*)^{p'}$.) The weight $\Lambda_S$ has trace $m$ (Lemma 3.11) and gives the gradient of the potential (Theorem 3.15).
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), eq. (20), p.22

import Mathlib
import Definitions.Def_MatrixLewis_maximizer

namespace MatrixLewis

/-- The right weight `W_S := Z_S^p` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), eq. (20), p.22). -/
noncomputable def rightWeight {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  mpow (pExp q) (maximizer q A S)

/-- The left weight `Γ_S := ∑ᵢⱼ (M*)ᵢⱼ Bᵢ Z_S Bⱼ` with `Bᵢ = Bᵢ(S)`, `M* = M*(S)`
(Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), eq. (20), p.22). -/
noncomputable def leftWeight {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i, ∑ j, dualMin q A S i j • (scaled A S i * maximizer q A S * scaled A S j)

/-- The **matrix Lewis weight** `Λ_S := ½(W_S + Γ_S)` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), eq. (20), p.22). -/
noncomputable def lewisWeight {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (rightWeight q A S + leftWeight q A S)

end MatrixLewis


