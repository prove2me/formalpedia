-- Prove2me | Definitions.Def_ErrAmpOV_kOV
-- name    : ErrAmpOV_kOV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:39.285824+00:00
-- url     : https://prove2.me/theorems/9b9b161b-2f00-4671-ad5c-dfbc74c5163a
-- title:
--   $k$-partite Orthogonal Vectors $k\text{-}\mathsf{OV}_{n,d}$
-- statement:
--   The input to $k\text{-}\mathsf{OV}_{n,d}$ is $k$ lists of $n$ vectors in $\{0,1\}^d$. The output is 1 iff one can pick one vector $a_j$ from each list $j$ with
--   $$
--   \sum_{\ell=1}^{d}\prod_{j=1}^{k}a_j[\ell]=0,
--   $$
--   i.e. every coordinate $\ell$ has some factor $a_j[\ell]=0$. For $k=2$ this is $\mathsf{OV}_{n,d}$. In this mission it occurs only in the brute-force bound of Fact 2.6.
--
--   **Formalization Note** The paper does not define $k$-OV formally; this is the standard $k$-partite version it describes on p.2. The input bits are indexed by `Fin k × Fin n × Fin d`.
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), p.2 and Fact 2.6, p.8

import Mathlib

set_option autoImplicit false

namespace ErrAmpOV

/-- The `k`-partite Orthogonal Vectors problem `k-OV_{n,d}`. The input is `k` lists of `n`
vectors in `{0,1}^d`; vector `i` of list `j` has coordinates `x (j, i, ·)`. `kOV k n d x = true`
iff one can pick one vector `a_j` from each list `j` with `Σ_l Π_j a_j[l] = 0`, i.e. every
coordinate `l` has a factor `a_j[l] = 0`.

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
p.2 (Theorem 1.2, "the `k`-partite version of OV", inputs of size `N = knd`) and Fact 2.6, p.8.

**Formalization Note.** The paper does not define `k`-OV formally; this is the standard
`k`-partite version. For `k = 2` it is `OV` on the same input type. -/
def kOV (k n d : ℕ) (x : Fin k × Fin n × Fin d → Bool) : Bool :=
  decide (∃ a : Fin k → Fin n, ∀ l : Fin d, ∃ j : Fin k, x (j, a j, l) = false)

end ErrAmpOV


