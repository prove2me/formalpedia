-- Prove2me | Definitions.Def_SPQPoly_SigmaSPQ
-- name    : SPQPoly_SigmaSPQ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:38:09.348335+00:00
-- url     : https://prove2.me/theorems/d94758e1-fb5d-4222-92af-ec532fd61084
-- title:
--   $\Sigma^{SPQ}_{n,d}$: sos SPQ polynomials of degree $d$ in $n$ variables
-- statement:
--   $\Sigma^{SPQ}_{n,d}$ is the set of SPQ polynomials $p$ in $n$ variables of degree $d$ that are sums of squares of polynomials. Clearly $\Sigma^{SPQ}_{n,d}\subseteq N^{SPQ}_{n,d}$.
--
--   **Formalization Note** Sos is `IsSumSq`; "degree $d$" is total degree exactly $d$; `SigmaSPQle` is the "at most $d$" reading. The squared polynomials need not be SPQ.
-- source:
--   Ahmadi, Dibek & Hall, Sums of Separable and Quadratic Polynomials, arXiv:2105.04766v1, §2.2, p.6

import Mathlib
import Definitions.Def_SPQPoly_IsSPQ

open MvPolynomial

namespace SPQPoly

/-- **The set `Σ^SPQ_{n,d}` of sos SPQ polynomials of degree `d` in `n` variables.**
Ahmadi, Dibek & Hall, *Sums of Separable and Quadratic Polynomials*, arXiv:2105.04766v1, §2.2,
p.6: "Σ^SPQ_{n,d} : the set of sos SPQ polynomials in n variables and degree d". Sum of squares is
defined on p.1: "there exist polynomials q1(x), . . . , qm(x) such that p(x) = Σ_{i=1}^m q_i^2(x)".

**Formalization Note.** Sos is Mathlib's `IsSumSq` (a finite sum of squares of polynomials, any
number of terms). "Degree d" is total degree exactly `d`; the companion `SigmaSPQle` uses total
degree at most `d`. -/
def SigmaSPQ (n d : ℕ) : Set (MvPolynomial (Fin n) ℝ) :=
  {p | IsSPQ p ∧ p.totalDegree = d ∧ IsSumSq p}

end SPQPoly


