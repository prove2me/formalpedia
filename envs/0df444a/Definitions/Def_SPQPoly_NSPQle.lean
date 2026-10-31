-- Prove2me | Definitions.Def_SPQPoly_NSPQle
-- name    : SPQPoly_NSPQle
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:37:58.850698+00:00
-- url     : https://prove2.me/theorems/75052013-7929-4045-82aa-784696f2efa7
-- title:
--   Nonnegative SPQ polynomials of degree at most $d$ in $n$ variables
-- statement:
--   The set of SPQ polynomials $p$ in $n$ variables of total degree **at most** $d$ with $p(x)\ge0$ for all $x\in\mathbb R^n$: the "at most $d$" reading of $N^{SPQ}_{n,d}$ (p.6).
-- source:
--   Ahmadi, Dibek & Hall, Sums of Separable and Quadratic Polynomials, arXiv:2105.04766v1, §2.2, p.6

import Mathlib
import Definitions.Def_SPQPoly_IsSPQ

open MvPolynomial

namespace SPQPoly

/-- **Nonnegative SPQ polynomials of degree at most `d` in `n` variables** (the "≤ d" reading of
`N^SPQ_{n,d}`).
Ahmadi, Dibek & Hall, *Sums of Separable and Quadratic Polynomials*, arXiv:2105.04766v1, §2.2,
p.6: "N^SPQ_{n,d} : the set of nonnegative SPQ polynomials in n variables and degree d".

**Formalization Note.** Same as `NSPQ` with `totalDegree ≤ d` in place of `totalDegree = d`. -/
def NSPQle (n d : ℕ) : Set (MvPolynomial (Fin n) ℝ) :=
  {p | IsSPQ p ∧ p.totalDegree ≤ d ∧ ∀ x : Fin n → ℝ, 0 ≤ eval x p}

end SPQPoly


