-- Prove2me | Definitions.Def_StengelZeroSum_extGame
-- name    : StengelZeroSum_extGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:47.494673+00:00
-- url     : https://prove2.me/theorems/1d342caa-efba-47b5-ad49-b01997306f67
-- title:
--   Dantzig's game with one extra row, $B_M$ (51)
-- statement:
--   Let $A$ be a real $m\times n$ matrix, $b\in\mathbb R^m$, $c\in\mathbb R^n$ and $M\in\mathbb R$. The zero-sum game $B_M$ is the $(m+n+2)\times(m+n+1)$ payoff matrix
--
--   $$
--   B_M=\begin{bmatrix} 0 & A & -b\\ -A^\top & 0 & c\\ b^\top & -c^\top & 0\\ \mathbf 1^\top & \mathbf 1^\top & -M\end{bmatrix}.
--   $$
--
--   Its columns belong to the minimizing column player and correspond to the variables $(y,x,t)\in\mathbb R^m\times\mathbb R^n\times\mathbb R$; its rows belong to the maximizing row player. The first $m+n+1$ rows form Dantzig's skew-symmetric game $B$ of (35); the last row $[\mathbf 1^\top,\mathbf 1^\top,-M]$ is the new row, which forces the column player to play the last column $t$ with positive probability whenever that is possible.
--
--   **Formalization Note** Columns are indexed by $(\mathrm{Fin}\,m\oplus\mathrm{Fin}\,n)\oplus\mathrm{Unit}$ in the order $(y,x,t)$; rows by $((\mathrm{Fin}\,m\oplus\mathrm{Fin}\,n)\oplus\mathrm{Unit})\oplus\mathrm{Unit}$, the two singleton rows being $[b^\top,-c^\top,0]$ and the new row.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Theorem 7, eq. (51), p.18

import Mathlib

open Matrix

namespace StengelZeroSum

/-- **Dantzig's game with one extra row**, the zero-sum game `B_M` of (51) in
von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6,
Theorem 7, eq. (51), p.18:
```
        y-cols   x-cols   t-col
B_M = [   0        A       −b  ]   m rows
      [  −A⊤       0        c  ]   n rows
      [   b⊤      −c⊤       0  ]   1 row
      [   1⊤       1⊤      −M  ]   1 row
```
The rows belong to the maximizing row player, the columns to the minimizing column player.

**Formalization Note** The `m + n + 1` columns are indexed by `(Fin m ⊕ Fin n) ⊕ Unit`, in the
order `(y, x, t)`: column `.inl (.inl i)` is `y_i`, `.inl (.inr j)` is `x_j`, `.inr ()` is `t`.
The `m + n + 2` rows are indexed by `((Fin m ⊕ Fin n) ⊕ Unit) ⊕ Unit`: `.inl (.inl (.inl i))`
is row `i` of the first block, `.inl (.inl (.inr j))` is row `j` of the second block,
`.inl (.inr ())` is the row `[b⊤, −c⊤, 0]`, and `.inr ()` is the new row `[1⊤, 1⊤, −M]`. -/
def extGame {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (M : ℝ) :
    Matrix (((Fin m ⊕ Fin n) ⊕ Unit) ⊕ Unit) ((Fin m ⊕ Fin n) ⊕ Unit) ℝ :=
  Matrix.of fun r s =>
    match r, s with
    | .inl (.inl (.inl _)), .inl (.inl _) => 0
    | .inl (.inl (.inl i)), .inl (.inr j) => A i j
    | .inl (.inl (.inl i)), .inr _ => -b i
    | .inl (.inl (.inr j)), .inl (.inl i) => -A i j
    | .inl (.inl (.inr _)), .inl (.inr _) => 0
    | .inl (.inl (.inr j)), .inr _ => c j
    | .inl (.inr _), .inl (.inl i) => b i
    | .inl (.inr _), .inl (.inr j) => -c j
    | .inl (.inr _), .inr _ => 0
    | .inr _, .inl (.inl _) => 1
    | .inr _, .inl (.inr _) => 1
    | .inr _, .inr _ => -M

end StengelZeroSum


