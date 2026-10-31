-- Prove2me | Definitions.Def_SPQPoly_NPoly
-- name    : SPQPoly_NPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:12.413004+00:00
-- url     : https://prove2.me/theorems/c5019d30-a198-4b7b-b723-faeb0e8660e8
-- title:
--   $N_{n,d}$: nonnegative polynomials of degree $d$ in $n$ variables
-- statement:
--   $N_{n,d}$ is the set of real polynomials $p$ in $n$ variables of degree $d$ that are **nonnegative**, i.e. $p(x)\ge0$ for all $x\in\mathbb R^n$.
--
--   It appears in Hilbert's Theorem 1.1, which compares it with the set $\Sigma_{n,d}$ of sums of squares.
--
--   **Formalization Note** "Degree $d$" is total degree exactly $d$. The "at most $d$" reading is the published cone `NieYangPareto.nonnegCone` with $K=\mathbb R^n$. $\mathbb R^n$ is `Fin n → ℝ`.
-- source:
--   Ahmadi, Dibek & Hall, Sums of Separable and Quadratic Polynomials, arXiv:2105.04766v1, §1, p.1

import Mathlib

open MvPolynomial

namespace SPQPoly

/-- **The set `N_{n,d}` of nonnegative polynomials of degree `d` in `n` variables.**
Ahmadi, Dibek & Hall, *Sums of Separable and Quadratic Polynomials*, arXiv:2105.04766v1, §1, p.1:
"A polynomial p : Rn → R with real coefficients is said to be nonnegative if p(x) ≥ 0 for all
x ∈ Rn … the set Nn,d of nonnegative polynomials of degree d in n variables".

**Formalization Note.** "Degree d" is total degree exactly `d`; the "≤ d" reading is the published
`NieYangPareto.nonnegCone Set.univ d`. -/
def NPoly (n d : ℕ) : Set (MvPolynomial (Fin n) ℝ) :=
  {p | p.totalDegree = d ∧ ∀ x : Fin n → ℝ, 0 ≤ eval x p}

end SPQPoly


