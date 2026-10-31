-- Prove2me | Definitions.Def_SPQPoly_SigmaPoly
-- name    : SPQPoly_SigmaPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:14.804917+00:00
-- url     : https://prove2.me/theorems/d8c97c68-6dd8-4a67-ae15-3019c88e6176
-- title:
--   $\Sigma_{n,d}$: sos polynomials of degree $d$ in $n$ variables
-- statement:
--   $\Sigma_{n,d}$ is the set of real polynomials $p$ in $n$ variables of degree $d$ that are **sums of squares (sos)**: there are polynomials $q_1,\dots,q_m$ with
--   $$
--   p(x)=\sum_{i=1}^m q_i(x)^2.
--   $$
--   Every sos polynomial is nonnegative, so $\Sigma_{n,d}\subseteq N_{n,d}$.
--
--   **Formalization Note** Sos is Mathlib's `IsSumSq` (any finite number of squares). "Degree $d$" is total degree exactly $d$; `SigmaPolyLe` is the "at most $d$" reading.
-- source:
--   Ahmadi, Dibek & Hall, Sums of Separable and Quadratic Polynomials, arXiv:2105.04766v1, §1, p.1

import Mathlib

open MvPolynomial

namespace SPQPoly

/-- **The set `Σ_{n,d}` of sos polynomials of degree `d` in `n` variables.**
Ahmadi, Dibek & Hall, *Sums of Separable and Quadratic Polynomials*, arXiv:2105.04766v1, §1, p.1:
"a sum of squares (sos) if there exist polynomials q1(x), . . . , qm(x) such that
p(x) = Σ_{i=1}^m q_i^2(x). It is clear that the set Σn,d of sos polynomials of degree d in n
variables …".

**Formalization Note.** Sos is `IsSumSq`; "degree d" is total degree exactly `d`; `SigmaPolyLe`
is the "≤ d" reading. -/
def SigmaPoly (n d : ℕ) : Set (MvPolynomial (Fin n) ℝ) :=
  {p | p.totalDegree = d ∧ IsSumSq p}

end SPQPoly


