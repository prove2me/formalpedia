-- Prove2me | Definitions.Def_MatrixLewis_rowOp
-- name    : MatrixLewis_rowOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:46.710147+00:00
-- url     : https://prove2.me/theorems/965f0103-0d45-4388-a255-b1c0ed395495
-- title:
--   Row operator $T v=(B_1v,\dots,B_mv)$
-- statement:
--   The **row operator** of symmetric $B_1,\dots,B_m\in\mathbb S^n$ is the linear map
--   $$
--   T:\mathbb R^n\to\mathbb R^m\otimes\mathbb R^n,\qquad Tv=(B_1v,\dots,B_mv).
--   $$
--   It satisfies $T^\top(M\otimes I_n)T=\sum_{i,j}M_{ij}B_iB_j$.
--
--   **Formalization Note** $\mathbb R^m\otimes\mathbb R^n$ is indexed by pairs $(i,a)\in\{1..m\}\times\{1..n\}$, so $T$ is the $(mn)\times n$ matrix with $T_{(i,a),b}=(B_i)_{ab}$; Kronecker products $M\otimes Y$ use the same index order.
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), §3.1, p.15

import Mathlib

namespace MatrixLewis

/-- The row operator `T : ℝⁿ → ℝᵐ ⊗ ℝⁿ`, `Tv = (B₁v, …, B_mv)`, of symmetric `B₁, …, B_m ∈ Sⁿ`
(Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), §3.1, p.15).

**Formalization Note** `ℝᵐ ⊗ ℝⁿ` is indexed by `Fin m × Fin n` (block `i`, row `a`), so `T`
is the `(m·n) × n` matrix with `T_{(i,a), b} = (Bᵢ)_{ab}`; Kronecker products `M ⊗ Y` use the
same index order (`Matrix.kroneckerMap`). -/
def rowOp {n m : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin m × Fin n) (Fin n) ℝ :=
  Matrix.of fun ia b => B ia.1 ia.2 b

end MatrixLewis


