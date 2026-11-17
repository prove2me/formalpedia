-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_sumLaw
-- name    : TwoFoldOPI_Supplement_sumLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:50:55.056946+00:00
-- url     : https://prove2.me/theorems/00a5975c-3a5a-4fea-b6df-c5d97590226f
-- title:
--   The law of a sum of independent integer random variables
-- statement:
--   For distributions $D_1,\dots,D_N$ on $\mathbb Z$, this is the distribution of $Z_1+\dots+Z_N$ for independent $Z_j\sim D_j$, i.e. the convolution $D_1*\cdots*D_N$ (the point mass at $0$ when $N=0$).
--
--   It is the law of the sum $Z$ in the local central limit theorem (Theorem 5.38).
--
--   **Formalization Note** Independence is built in: the law is the iterated convolution of probability mass functions.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.4, Theorem 5.38, p. 34

import Mathlib

namespace TwoFoldOPI

namespace Supplement

/-- **The law of a sum of independent integer random variables.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.4, Theorem 5.38, p.34: "Let {Z_{r,i} : r ∈ [R], i ∈ [n_r]} be n independent random
variables with Z_{r,i} ∼ D_r for all i. Let Z = Σ_{r∈[R]} Σ_{i∈[n_r]} Z_{r,i}."

For a list `[D_1, …, D_N]` of distributions on `ℤ`, `sumLaw` is the distribution of
`Z_1 + ⋯ + Z_N` for independent `Z_j ∼ D_j` (the convolution `D_1 ∗ ⋯ ∗ D_N`); the empty list gives
the point mass at `0`.

**Formalization Note.** Independence is built in: the law is the iterated convolution, computed by
`PMF.bind`. -/
noncomputable def sumLaw : List (PMF ℤ) → PMF ℤ
  | [] => PMF.pure 0
  | D :: Ds => D.bind fun a => (sumLaw Ds).map fun b => a + b

end Supplement

end TwoFoldOPI


