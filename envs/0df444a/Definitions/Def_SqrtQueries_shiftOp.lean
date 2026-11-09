-- Prove2me | Definitions.Def_SqrtQueries_shiftOp
-- name    : SqrtQueries_shiftOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:28:47.444664+00:00
-- url     : https://prove2.me/theorems/e8c3c7b2-c753-444e-adc8-ef86f4c63b39
-- title:
--   Shift operator $S|j\rangle=|j+1\rangle$ on $\mathbb C^N$
-- statement:
--   Fix an integer $N\ge 1$ and index the standard basis of $\mathbb C^N$ by $j\in\{0,\dots,N-1\}$. The **shift operator** is the permutation matrix $S$ with
--   $$
--   S|j\rangle=|j+1\rangle,
--   $$
--   where the addition $j+1$ is taken modulo $N$. Equivalently, the entry of $S$ in row $i$ and column $j$ is $1$ if $i\equiv j+1 \pmod N$ and $0$ otherwise.
--
--   Together with the clock operator, $S$ is one of the two generalized Pauli matrices; here it enters through the Hermitian matrix $A=(S+S^\dagger)/2$ of Definition 3.2.
--
--   **Formalization Note** The basis is `Fin N` with `[NeZero N]`, so `j + 1` is addition modulo $N$. The matrix is `S i j = if i = j + 1 then 1 else 0`.
-- source:
--   Ma–Tang, Square-root queries can help, STOC 2027 submission (manuscript sha256 783868e7…c5f15a), Section 2.1, p.10

import Mathlib

namespace SqrtQueries

/-- The **shift operator** `S` on `ℂ^N` (Ma–Tang, *Square-root queries can help*, STOC 2027
submission manuscript, sha256 783868e7…c5f15a, Section 2.1, p.10): `S|j⟩ = |j + 1⟩`, addition
modulo `N`.

**Formalization Note.** The basis of `ℂ^N` is `Fin N` (`[NeZero N]`, so `N ≥ 1`), and `j + 1` is
`Fin` addition, which is addition modulo `N`. As a matrix, `S i j = 1` exactly when `i = j + 1`,
so that the column `j` of `S` is the basis vector `e_{j+1}` (`S|j⟩ = |j+1⟩`). -/
def shiftOp (N : ℕ) [NeZero N] : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => if i = j + 1 then 1 else 0

end SqrtQueries


