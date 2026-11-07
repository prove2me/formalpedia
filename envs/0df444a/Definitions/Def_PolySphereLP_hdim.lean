-- Prove2me | Definitions.Def_PolySphereLP_hdim
-- name    : PolySphereLP_hdim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:20.890331+00:00
-- url     : https://prove2.me/theorems/02d702c8-de69-4366-b4a3-37288aee7b07
-- title:
--   The dimension $h_{n,j}$ of $\mathcal H_{n,j}$
-- statement:
--   For integers $n\ge1$ and $j\ge0$,
--   $$h_{n,j}=\binom{n+j-1}{j}-\binom{n+j-3}{j-2},$$
--   where the second term is zero for $j<2$. This is $\dim\mathcal H_{n,j}$; for example $h_{n,0}=1$, $h_{n,1}=n$ and $h_{3,2}=5$. The paper writes $h=h_{n,d}$ and $H=h_{n,q}$.
--
--   **Formalization Note** A natural number. The case split implements "the second term is zero for $j<2$" (in $\mathbb N$, $\binom{n+j-3}{j-2}$ would otherwise be $1$ at $j=0$); for $j\ge2$ the subtraction is never truncated.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), (13), p.10

import Mathlib

namespace PolySphereLP

/-- **The dimension `h_{n,j}` of `ℋ_{n,j}`.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), (13), p.10:
`h_{n,j} = (n+j−1 choose j) − (n+j−3 choose j−2)`, "The second term is zero for j < 2."

**Formalization Note.** The guard `j < 2` implements "the second term is zero": in `ℕ`,
`(n+j−3).choose (j−2)` would be `1` at `j = 0`. For `j ≥ 2` the subtraction is never truncated
(`n ≥ 1`), since `(n+j−1 choose j)` counts the degree-`j` monomials and dominates the degree-`(j−2)`
count. Sanity: `hdim n 0 = 1`, `hdim n 1 = n`. -/
def hdim (n j : ℕ) : ℕ :=
  if j < 2 then (n + j - 1).choose j else (n + j - 1).choose j - (n + j - 3).choose (j - 2)

end PolySphereLP


