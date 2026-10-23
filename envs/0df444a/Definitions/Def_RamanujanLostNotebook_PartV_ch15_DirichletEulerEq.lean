-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_ch15_DirichletEulerEq
-- name    : RamanujanLostNotebook_PartV_ch15_DirichletEulerEq
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T18:33:31.933388+00:00
-- url     : https://prove2.me/theorems/111a38a0-7ff9-4b8b-8e44-2dcf2d62e518
-- title:
--   Ramanujan's Lost Notebook Part V, Ch. 15: DirichletEulerEq
-- statement:
--   `DirichletEulerEq c F s`: the Dirichlet series `∑_{n ≥ 1} c(n) n^{-s}` and the product
--   `∏_p F(p)` over ALL primes `p` both converge unconditionally (`HasSum`, `HasProd`: the limit
--   along finite sets, equivalent to absolute convergence of the series) and have the same value.
--   This is the meaning given in this chapter to an identity "Dirichlet series = Euler product"
--   such as (15.2.2), p. 323.  A product printed over a subset of the primes is expressed by a
--   factor `F p` that equals `1` at the other primes.
--   The series is indexed by `n = m + 1`, `m : ℕ`, so `c 0` plays no role; `((m : ℂ) + 1) ^ s` is
--   the complex power of a positive integer, `exp (s log (m + 1))`.
--   A proposition, total, no junk: it is false when either side fails to converge.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 15.

import Mathlib

namespace RamanujanLostNotebook.PartV

/-- `DirichletEulerEq c F s`: the Dirichlet series `∑_{n ≥ 1} c(n) n^{-s}` and the product
`∏_p F(p)` over ALL primes `p` both converge unconditionally (`HasSum`, `HasProd`: the limit
along finite sets, equivalent to absolute convergence of the series) and have the same value.
This is the meaning given in this chapter to an identity "Dirichlet series = Euler product"
such as (15.2.2), p. 323.  A product printed over a subset of the primes is expressed by a
factor `F p` that equals `1` at the other primes.
The series is indexed by `n = m + 1`, `m : ℕ`, so `c 0` plays no role; `((m : ℂ) + 1) ^ s` is
the complex power of a positive integer, `exp (s log (m + 1))`.
A proposition, total, no junk: it is false when either side fails to converge. -/
def DirichletEulerEq (c : ℕ → ℂ) (F : Nat.Primes → ℂ) (s : ℂ) : Prop :=
  ∃ L : ℂ, HasSum (fun m : ℕ => c (m + 1) / ((m : ℂ) + 1) ^ s) L ∧ HasProd F L

end RamanujanLostNotebook.PartV


