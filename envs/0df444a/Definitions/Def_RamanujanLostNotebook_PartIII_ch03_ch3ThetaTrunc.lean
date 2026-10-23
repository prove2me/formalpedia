-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch03_ch3ThetaTrunc
-- name    : RamanujanLostNotebook_PartIII_ch03_ch3ThetaTrunc
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T09:01:20.942401+00:00
-- url     : https://prove2.me/theorems/9d205c1d-b93c-4570-b02c-53ae8bb1b40a
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 3: ch3ThetaTrunc
-- statement:
--   A finite representative of f(-q^r,-q^s) in all degrees at most N, for r,s>0.
--   The k-th term is (-1)^k X^(r*k*(k+1)/2+s*k*(k-1)/2). Both triangular
--   numbers are nonnegative for every integer k. Terms outside [-N-1,N+1]
--   have degree >N, so extracting degree N is an exact source coefficient.
--   The definition is a polynomial representative, never the analytic theta value.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 3.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- A finite representative of f(-q^r,-q^s) in all degrees at most N, for r,s>0.
The k-th term is (-1)^k X^(r*k*(k+1)/2+s*k*(k-1)/2). Both triangular
numbers are nonnegative for every integer k. Terms outside [-N-1,N+1]
have degree >N, so extracting degree N is an exact source coefficient.
The definition is a polynomial representative, never the analytic theta value. -/
noncomputable def ch3ThetaTrunc {R : Type*} [CommRing R] (N r s : ℕ) : Polynomial R :=
  ∑ k ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1),
    Polynomial.C ((-1 : R) ^ k.natAbs) * Polynomial.X ^
      ((r : ℤ) * (k * (k + 1) / 2) + (s : ℤ) * (k * (k - 1) / 2)).toNat

end RamanujanLostNotebook.PartIII

end


