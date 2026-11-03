-- Prove2me | Definitions.Def_NearestDSM_Amat
-- name    : NearestDSM_Amat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:37.037894+00:00
-- url     : https://prove2.me/theorems/fec2a757-5860-4a0e-ab18-9485da39a651
-- title:
--   The constraint matrix $A\in\mathbb R^{(2n-1)\times n^2}$
-- statement:
--   The equality constraints $Xe=e$ and $X^Te=e$ of the nearest doubly stochastic matrix problem, written for $x=\mathrm{vec}(X)\in\mathbb R^{n^2}$, are $\bar Ax=\bar e$ with
--   $$
--   \bar A=\begin{pmatrix}I\otimes e^T\\ e^T\otimes I\end{pmatrix}\in\mathbb R^{2n\times n^2}.
--   $$
--   The first $n$ rows are the column-sum constraints (column sums appear first), the last $n$ rows the row-sum constraints. The matrix $A\in\mathbb R^{(2n-1)\times n^2}$ is $\bar A$ with its last row (the constraint that the last row of $X$ sums to one) discarded.
--
--   Concretely, the row of $A$ for column $j$ has a $1$ at every entry $(i,j)$, and the row of $A$ for row $i\le n-1$ has a $1$ at every entry $(i,j)$; all other entries are $0$.
--
--   **Formalization Note** The paper's $n$ is $n+1$. Vectors in $\mathbb R^{n^2}$ are indexed by the pair (row, column), so the column-stacking order of $\mathrm{vec}$ plays no role.
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, displays (1.2)-(1.3), pp.3-4

import Mathlib
open Matrix

namespace NearestDSM

/-- The constraint matrix `A ∈ ℝ^{(2n−1)×n²}` of problem (1.3), Hu, Im, Li & Wolkowicz, *A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem*, arXiv:2107.09631v1, (1.2)–(1.3),
pp.3–4: the matrix `Ā = [I ⊗ eᵀ; eᵀ ⊗ I]` of the column-sum and row-sum constraints of `X`
("the column sum constraints appear first"), with its last row (the constraint that the last row
of `X` sums to one) discarded.

Row `Sum.inl j` is the column-sum constraint of column `j`: it has a `1` at every entry `(a, j)`.
Row `Sum.inr i` is the row-sum constraint of row `Fin.castSucc i`: it has a `1` at every entry
`(Fin.castSucc i, b)`.

**Formalization Note.** The paper's size `n` is `n + 1`. A vector `x = vec(X) ∈ ℝ^{n²}` is
indexed by the pair `(row, column) : Fin (n+1) × Fin (n+1)`; the column-stacking order of `vec`
plays no role once entries are indexed by pairs. -/
def Amat (n : ℕ) : Matrix (Fin (n + 1) ⊕ Fin n) (Fin (n + 1) × Fin (n + 1)) ℝ :=
  Matrix.of fun i p =>
    Sum.elim (fun j => if p.2 = j then (1 : ℝ) else 0)
      (fun r => if p.1 = Fin.castSucc r then (1 : ℝ) else 0) i

end NearestDSM


