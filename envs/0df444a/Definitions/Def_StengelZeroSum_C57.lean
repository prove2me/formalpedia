-- Prove2me | Definitions.Def_StengelZeroSum_C57
-- name    : StengelZeroSum_C57
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:49.305764+00:00
-- url     : https://prove2.me/theorems/3ba5479f-dcd3-4e95-abd3-10627ad0bb39
-- title:
--   The skew-symmetric matrix $C$ of (57)
-- statement:
--   For a real $m\times n$ matrix $A$, the $(m+n)\times(m+n)$ matrix
--
--   $$
--   C=\begin{bmatrix}0 & A\\ -A^\top & 0\end{bmatrix}.
--   $$
--
--   It satisfies $C=-C^\top$ and is the matrix to which Theorem 8 is applied in the proof of Theorem 7.
--
--   **Formalization Note** Both index sets are $\mathrm{Fin}\,m\oplus\mathrm{Fin}\,n$, the $m$-block first.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, eq. (57), p.20

import Mathlib

open Matrix

namespace StengelZeroSum

/-- The skew-symmetric matrix `C` of (57),
von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, eq. (57),
p.20: `C = [ 0 A ; −A⊤ 0 ]`.

**Formalization Note** `C` is indexed by `Fin m ⊕ Fin n` on both sides (the `y`-block first,
then the `x`-block), built with `Matrix.fromBlocks`. -/
def C57 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
  Matrix.fromBlocks 0 A (-Aᵀ) 0

end StengelZeroSum


