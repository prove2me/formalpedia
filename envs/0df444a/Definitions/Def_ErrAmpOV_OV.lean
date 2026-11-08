-- Prove2me | Definitions.Def_ErrAmpOV_OV
-- name    : ErrAmpOV_OV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:38.201681+00:00
-- url     : https://prove2.me/theorems/384c8784-9216-454b-ba9c-1bf6c9dfcade
-- title:
--   Orthogonal Vectors $\mathsf{OV}_{n,d}$ (Definition 2.4)
-- statement:
--   The input to $\mathsf{OV}_{n,d}$ is two lists $A=(a_1,\dots,a_n)$ and $B=(b_1,\dots,b_n)$ of vectors in $\{0,1\}^d$, that is $2nd$ bits in total. The output is
--   $$
--   \mathsf{OV}_{n,d}(A,B)=1\iff \exists\, i,j:\ a_i\cdot b_j=0\ \text{ over }\mathbb Z .
--   $$
--
--   For 0/1 vectors, $a\cdot b=0$ means that no coordinate has both entries equal to 1. This is the central problem of the mission.
--
--   **Formalization Note** The input bits are indexed by `Fin 2 × Fin n × Fin d`, with $A$ the rows of index 0 and $B$ the rows of index 1. The lists may contain repeated vectors. At $d=0$ every pair is orthogonal.
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), Definition 2.4, p.8

import Mathlib

set_option autoImplicit false

namespace ErrAmpOV

/-- The Orthogonal Vectors problem `OV_{n,d}` (Definition 2.4). The input is two lists
`A = (a_0, …, a_{n-1})` and `B = (b_0, …, b_{n-1})` of vectors in `{0,1}^d`, with
`a_i[k] = x (0, i, k)` and `b_j[k] = x (1, j, k)`. `OV n d x = true` iff some `a_i`, `b_j` are
orthogonal over `ℤ`, i.e. no coordinate `k` has `a_i[k] = b_j[k] = 1`.

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
Definition 2.4, p.8.

**Formalization Note.** The input has `2nd` bits, indexed by `Fin 2 × Fin n × Fin d`. The lists
may contain repeated vectors (the page's "`A, B ⊂ {0,1}^d`" with `A = {a_1, …, a_n}` counts `n`
entries each). For `0/1` vectors, `a · b = 0` over `ℤ` iff no coordinate has both entries `1`. -/
def OV (n d : ℕ) (x : Fin 2 × Fin n × Fin d → Bool) : Bool :=
  decide (∃ i j : Fin n, ∀ k : Fin d, ¬ (x (0, i, k) = true ∧ x (1, j, k) = true))

end ErrAmpOV


