-- Prove2me | Definitions.Def_FreeSpencer_layout
-- name    : FreeSpencer_layout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:03:13.515779+00:00
-- url     : https://prove2.me/theorems/405a1470-28bb-4f7b-bcff-9f7a99e0e162
-- title:
--   The input layout of the machine
-- statement:
--   The machine's input is the list $n,m,b$ of real numbers followed by the entries of $A_1,\dots,A_n$, row by row.
--
--   **Formalization Note** The theorem fixes no layout. Index cells start at zero, so a program reads $n,m,b$ by a counting loop in $O(n+m+b)$ steps, within the polynomial time bound.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Theorem 1.1, p.2; Definition B.1, p.74

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM

namespace FreeSpencer

/-- The machine's input: the reals `n, m, b`, then the entries of `A 0, …, A (n-1)` row by row.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Theorem 1.1, p.2; Definition B.1, p.74.

**Formalization Note** The theorem fixes no layout. Index cells start at `0`, so the program reads
`n, m, b` by a counting loop: it steps an index cell and a real cell together until `rblt` says the
real cell has reached the input, in `O(n + m + b)` steps, inside the time bound. -/
noncomputable def layout (n m b : ℕ) (A : Fin n → Matrix (Fin m) (Fin m) ℝ) : List ℝ :=
  [(n : ℝ), (m : ℝ), (b : ℝ)] ++ (List.finRange n).flatMap fun i => MatMulTimeLP.matToList (A i)

end FreeSpencer


