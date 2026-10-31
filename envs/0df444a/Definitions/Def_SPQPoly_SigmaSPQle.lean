-- Prove2me | Definitions.Def_SPQPoly_SigmaSPQle
-- name    : SPQPoly_SigmaSPQle
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:37:59.857731+00:00
-- url     : https://prove2.me/theorems/ad054be0-1aa7-4e12-b8a8-7d76a934fb87
-- title:
--   Sos SPQ polynomials of degree at most $d$ in $n$ variables
-- statement:
--   The set of SPQ polynomials $p$ in $n$ variables of total degree **at most** $d$ that are sums of squares: the "at most $d$" reading of $\Sigma^{SPQ}_{n,d}$ (p.6).
--
--   **Formalization Note** Sos is `IsSumSq`.
-- source:
--   Ahmadi, Dibek & Hall, Sums of Separable and Quadratic Polynomials, arXiv:2105.04766v1, §2.2, p.6

import Mathlib
import Definitions.Def_SPQPoly_IsSPQ

open MvPolynomial

namespace SPQPoly

/-- **Sos SPQ polynomials of degree at most `d` in `n` variables** (the "≤ d" reading of
`Σ^SPQ_{n,d}`).
Ahmadi, Dibek & Hall, *Sums of Separable and Quadratic Polynomials*, arXiv:2105.04766v1, §2.2,
p.6: "Σ^SPQ_{n,d} : the set of sos SPQ polynomials in n variables and degree d".

**Formalization Note.** Same as `SigmaSPQ` with `totalDegree ≤ d` in place of
`totalDegree = d`; sos is `IsSumSq`. -/
def SigmaSPQle (n d : ℕ) : Set (MvPolynomial (Fin n) ℝ) :=
  {p | IsSPQ p ∧ p.totalDegree ≤ d ∧ IsSumSq p}

end SPQPoly


