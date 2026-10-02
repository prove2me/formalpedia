-- Prove2me | Definitions.Def_AppliedComb_ManyFaces_dualPartition
-- name    : AppliedComb_ManyFaces_dualPartition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:45:51.177028+00:00
-- url     : https://prove2.me/theorems/230bab29-7ae8-4708-96f0-7ddec8bb8fbc
-- title:
--   The dual partition V^d (Section 16.5)
-- statement:
--   Let $V = (v_1, v_2, \dots, v_m)$ be a partition of $t$. Its **dual partition** $V^d = (w_1, w_2, \dots, w_n)$ has $n = v_1$ entries, and for $j = 1, \dots, n$
--   $$w_j = \#\{\, i : v_i \ge j \,\},$$
--   the number of entries of $V$ that are at least $j$. It is again a partition of $t$ (the conjugate partition: its Ferrers diagram is the transpose of that of $V$), and $(V^d)^d = V$. For example, the dual of $(8, 6, 6, 6, 5, 5, 3, 1, 1, 1)$ is $(10, 7, 7, 6, 6, 4, 1, 1)$; both are partitions of $42$.
--
--   The dual partition is the benchmark in the Gale–Ryser Theorem 16.12: pushing the ones of every row of a zero–one matrix with row sum string $R$ to the left produces column sums $R^d$.
--
--   **Formalization Note.** The page prints the rule as "$w_j$ is the number of entries in $V$ that are at least $n + 1 - j$". That lists the same numbers in increasing order, which is not a partition string. The page's example, $(8,6,6,6,5,5,3,1,1,1) \mapsto (8,7,7,6,6,4,1,1)$, is also misprinted: its right side sums to $40$, not $42$. The definition takes the conjugate partition in non-increasing order, which is the only reading under which Theorem 16.12 holds. `dual V` is the list whose position $j-1$ holds $w_j$; the empty string has empty dual.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 324, Section 16.5 (dual partition; misprinted on the page, read as the conjugate partition)

import Mathlib

namespace AppliedComb.ManyFaces

/-- The dual (conjugate) partition `V^d` of `V = (v_1, …, v_m)` (Keller & Trotter, *Applied
Combinatorics* (2017 Edition), p. 324): the string `W = (w_1, …, w_n)` with `n = v_1` and, for
`j = 1, …, n`, `w_j` the number of entries of `V` that are at least `j`. In the list, position
`j - 1` holds `w_j`. For the empty string, `v_1` is taken to be `0` and the dual is empty.

The page prints "at least `n + 1 − j`", which lists the same numbers in increasing order and so is
not a partition string; its own example has the non-increasing order of this definition. -/
def dual (V : List ℕ) : List ℕ :=
  (List.range (V.headD 0)).map fun j => V.countP fun v => j + 1 ≤ v

end AppliedComb.ManyFaces


