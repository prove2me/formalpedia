-- Prove2me | Definitions.Def_AppliedComb_ManyFaces_zeroOneMatrix
-- name    : AppliedComb_ManyFaces_zeroOneMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:46:15.381572+00:00
-- url     : https://prove2.me/theorems/e0b37559-067f-424f-889f-b1b9369e58a6
-- title:
--   Zero–one matrix with given row and column sum strings (Section 16.5)
-- statement:
--   Let $R = (r_1, \dots, r_m)$ and $C = (c_1, \dots, c_n)$ be strings of non-negative integers. An $m \times n$ matrix $M = (m_{i,j})$ is a **zero–one matrix with row sum string $R$ and column sum string $C$** if every entry is $0$ or $1$ and
--   $$\sum_{1 \le j \le n} m_{i,j} = r_i \quad (1 \le i \le m), \qquad \sum_{1 \le i \le m} m_{i,j} = c_j \quad (1 \le j \le n).$$
--   The number of rows is the length of $R$ and the number of columns is the length of $C$.
--
--   Existence of such a matrix is the question answered by the Gale–Ryser Theorem 16.12.
--
--   **Formalization Note.** `IsZeroOneMatrixWithSums R C M` takes `M : Matrix (Fin R.length) (Fin C.length) ℕ`; rows and columns are indexed from $0$, so Lean's row $i$ is the book's row $i+1$. Entries are natural numbers restricted to $\{0, 1\}$.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 323, Section 16.5 (row sum string, column sum string)

import Mathlib

namespace AppliedComb.ManyFaces

/-- A zero–one matrix with row sum string `R = (r_1, …, r_m)` and column sum string
`C = (c_1, …, c_n)` (Keller & Trotter, *Applied Combinatorics* (2017 Edition), p. 323): an
`m × n` matrix `M`, with `m` the length of `R` and `n` the length of `C`, whose entries are all
`0` or `1`, such that row `i` sums to `r_i` and column `j` sums to `c_j`. Rows and columns are
indexed from `0` (`Fin m`, `Fin n`); row `i` corresponds to the book's row `i + 1`. -/
def IsZeroOneMatrixWithSums (R C : List ℕ) (M : Matrix (Fin R.length) (Fin C.length) ℕ) : Prop :=
  (∀ i j, M i j = 0 ∨ M i j = 1) ∧
    (∀ i, ∑ j, M i j = R.get i) ∧
    (∀ j, ∑ i, M i j = C.get j)

end AppliedComb.ManyFaces


