-- Prove2me | Definitions.Def_RamanujanNotebooks_ch07_ch07BernoulliStar
-- name    : RamanujanNotebooks_ch07_ch07BernoulliStar
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T01:04:33.498694+00:00
-- url     : https://prove2.me/theorems/c4f58edb-56b1-447f-b4cf-1c9bd365e0bd
-- title:
--   Ramanujan's Notebooks, Part I, Ch. 7: ch07BernoulliStar
-- statement:
--   Ramanujan's Bernoulli number of arbitrary index, `B*_r`, defined by (1.7), p. 151:
--   `ζ(r) = (2π)^r B*_r / (2 Γ(r + 1))`, that is `B*_r = 2 Γ(r + 1) ζ(r) / (2π)^r`.
--   For an even positive integer `r = 2n` it is `(-1)^{n-1} B_{2n} = |B_{2n}|`.
--
--   Domain: complex `r` outside `1` and the negative integers.  At `r = 1` and at
--   `r = -1, -3, -5, …` the function has a pole.  At `r = -2, -4, -6, …` the pole of `Γ(r + 1)`
--   is cancelled by a zero of `ζ(r)` and the book's `B*_r` is the finite limit (Corollary 1 of
--   Section 4: `B*_{-2} = 2ζ(3)`), but this expression is NOT that limit: Mathlib's
--   `Complex.Gamma` is `0` at its poles, so the value here is `0`.  At `r = 1` Mathlib's
--   `riemannZeta 1` is a conventional finite number and the value is meaningless.
--   Statements must exclude `r = 1` and the negative integers, or take a limit.
--   Reference: `B*_2 = 1/6`, `B*_4 = 1/30`, `B*_0 = -1`, `B*_{1/2} = -1.03262657611…`,
--   `B*_{3/2} = 0.44099327819…`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 7.

import Mathlib

namespace RamanujanNotebooks

/-- Ramanujan's Bernoulli number of arbitrary index, `B*_r`, defined by (1.7), p. 151:
`ζ(r) = (2π)^r B*_r / (2 Γ(r + 1))`, that is `B*_r = 2 Γ(r + 1) ζ(r) / (2π)^r`.
For an even positive integer `r = 2n` it is `(-1)^{n-1} B_{2n} = |B_{2n}|`.

Domain: complex `r` outside `1` and the negative integers.  At `r = 1` and at
`r = -1, -3, -5, …` the function has a pole.  At `r = -2, -4, -6, …` the pole of `Γ(r + 1)`
is cancelled by a zero of `ζ(r)` and the book's `B*_r` is the finite limit (Corollary 1 of
Section 4: `B*_{-2} = 2ζ(3)`), but this expression is NOT that limit: Mathlib's
`Complex.Gamma` is `0` at its poles, so the value here is `0`.  At `r = 1` Mathlib's
`riemannZeta 1` is a conventional finite number and the value is meaningless.
Statements must exclude `r = 1` and the negative integers, or take a limit.
Reference: `B*_2 = 1/6`, `B*_4 = 1/30`, `B*_0 = -1`, `B*_{1/2} = -1.03262657611…`,
`B*_{3/2} = 0.44099327819…`. -/
noncomputable def ch07BernoulliStar (r : ℂ) : ℂ :=
  2 * Complex.Gamma (r + 1) * riemannZeta r / (2 * (Real.pi : ℂ)) ^ r

end RamanujanNotebooks


