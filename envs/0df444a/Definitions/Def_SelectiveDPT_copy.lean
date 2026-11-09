-- Prove2me | Definitions.Def_SelectiveDPT_copy
-- name    : SelectiveDPT_copy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:48:51.786198+00:00
-- url     : https://prove2.me/theorems/059fb7c2-4a0a-4d97-83a8-2b294a643a7a
-- title:
--   The $j$-th copy $x_j$ of an $m$-copy input
-- statement:
--   An $m$-copy input $x = (x_1, \dots, x_m) \in (X^\iota)^m$ is written as a function on $[m] \times \iota$ (copy, position). Its **$j$-th copy** is $x_j = (x(j,i))_{i \in \iota} \in X^\iota$.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Definition 1.1, p.3; footnote 5, p.9

import Mathlib

namespace SelectiveDPT

/-- The `j`-th copy `x_j ∈ X^n` of an `m`-copy input `x = (x_1, …, x_m) ∈ (X^n)^m`
(arXiv:2609.26678, Definition 1.1, p.3).

**Formalization Note.** An `m`-copy input is a function on `Fin m × ι` (copy, position), as in
footnote 5, p.9 ("we will … simply write it as a tuple `(i, j)`, where `i ∈ [m]` now denotes which
copy we are querying, and `j ∈ [n]` denotes the index we query within that copy"). -/
def copy {m : ℕ} {ι α : Type*} (x : Fin m × ι → α) (j : Fin m) : ι → α :=
  fun i => x (j, i)

end SelectiveDPT


