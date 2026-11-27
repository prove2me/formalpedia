-- Prove2me | Definitions.Def_StengelZeroSum_Supplement_dantzigGame
-- name    : StengelZeroSum_Supplement_dantzigGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:25:54.997868+00:00
-- url     : https://prove2.me/theorems/dd5eb72d-2678-4d0a-82bb-382e8dcd8ca3
-- title:
--   Dantzig's game $B$ (35)
-- statement:
--   Let $A$ be a real $m\times n$ matrix, $b\in\mathbb R^m$ and $c\in\mathbb R^n$. **Dantzig's game** is the zero-sum game with the $k\times k$ payoff matrix, $k=m+n+1$,
--
--   $$
--   B=\begin{bmatrix} 0 & A & -b\\ -A^\top & 0 & c\\ b^\top & -c^\top & 0\end{bmatrix}. \tag{35}
--   $$
--
--   Rows belong to the maximizing row player and columns to the minimizing column player; both are indexed by the variables $(y,x,t)\in\mathbb R^m\times\mathbb R^n\times\mathbb R$. The matrix is skew-symmetric, $B=-B^\top$, so the game is symmetric. Theorem 5 reads optimal solutions of the LP pair (1), (2), or a certificate of infeasibility, from a min-max strategy of $B$.
--
--   **Formalization Note** Rows and columns are indexed by $(\mathrm{Fin}\,m\oplus\mathrm{Fin}\,n)\oplus\mathrm{Unit}$ in the order $(y,x,t)$; the last index is the paper's $k$th coordinate $t$. These are the columns of the published game $B_M$ of (51) (`StengelZeroSum.extGame`), whose first $m+n+1$ rows are $B$.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Theorem 5, eq. (35), p.13

import Mathlib

open Matrix

namespace StengelZeroSum.Supplement

/-- **Dantzig's game** `B` of (35), von Stengel, *Zero-Sum Games and Linear Programming
Duality*, arXiv:2205.11196v6, Theorem 5, eq. (35), p.13: for `A ∈ ℝ^{m×n}`, `b ∈ ℝ^m`,
`c ∈ ℝ^n`, the `k × k` payoff matrix, `k = m + n + 1`,
```
        y-cols   x-cols   t-col
B = [    0        A       −b  ]   m rows
    [   −A⊤       0        c  ]   n rows
    [    b⊤      −c⊤       0  ]   1 row
```
The rows belong to the maximizing row player, the columns to the minimizing column player.
`B = −B⊤` (skew-symmetric).

**Formalization Note** Rows and columns are both indexed by `(Fin m ⊕ Fin n) ⊕ Unit`, in the
order `(y, x, t)`: `.inl (.inl i)` is `y_i`, `.inl (.inr j)` is `x_j`, `.inr ()` is `t`, the
paper's `k`th coordinate. This is the column type of the published `StengelZeroSum.extGame`
(51), whose first `m + n + 1` rows are this matrix. -/
def dantzigGame {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Matrix ((Fin m ⊕ Fin n) ⊕ Unit) ((Fin m ⊕ Fin n) ⊕ Unit) ℝ :=
  Matrix.of fun r s =>
    match r, s with
    | .inl (.inl _), .inl (.inl _) => 0
    | .inl (.inl i), .inl (.inr j) => A i j
    | .inl (.inl i), .inr _ => -b i
    | .inl (.inr j), .inl (.inl i) => -A i j
    | .inl (.inr _), .inl (.inr _) => 0
    | .inl (.inr j), .inr _ => c j
    | .inr _, .inl (.inl i) => b i
    | .inr _, .inl (.inr j) => -c j
    | .inr _, .inr _ => 0

end StengelZeroSum.Supplement


