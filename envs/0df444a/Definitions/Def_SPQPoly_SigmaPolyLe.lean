-- Prove2me | Definitions.Def_SPQPoly_SigmaPolyLe
-- name    : SPQPoly_SigmaPolyLe
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:18.440874+00:00
-- url     : https://prove2.me/theorems/125f6374-96ff-4078-9b3e-16a3c73a51a3
-- title:
--   Sos polynomials of degree at most $d$ in $n$ variables
-- statement:
--   The set of real polynomials $p$ in $n$ variables of total degree **at most** $d$ that are sums of squares of polynomials.
--
--   This is the reading of $\Sigma_{n,d}$ (p.1) in which "degree $d$" means "degree at most $d$"; its nonnegative counterpart is the published cone `NieYangPareto.nonnegCone` with $K=\mathbb R^n$.
--
--   **Formalization Note** Sos is Mathlib's `IsSumSq`.
-- source:
--   Ahmadi, Dibek & Hall, Sums of Separable and Quadratic Polynomials, arXiv:2105.04766v1, §1, p.1

import Mathlib

open MvPolynomial

namespace SPQPoly

/-- **Sos polynomials of degree at most `d` in `n` variables** (the "≤ d" reading of `Σ_{n,d}`).
Ahmadi, Dibek & Hall, *Sums of Separable and Quadratic Polynomials*, arXiv:2105.04766v1, §1, p.1:
"the set Σn,d of sos polynomials of degree d in n variables".

**Formalization Note.** Same as `SigmaPoly` with `totalDegree ≤ d`; sos is `IsSumSq`. -/
def SigmaPolyLe (n d : ℕ) : Set (MvPolynomial (Fin n) ℝ) :=
  {p | p.totalDegree ≤ d ∧ IsSumSq p}

end SPQPoly


