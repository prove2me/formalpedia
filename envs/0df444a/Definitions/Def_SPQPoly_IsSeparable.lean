-- Prove2me | Definitions.Def_SPQPoly_IsSeparable
-- name    : SPQPoly_IsSeparable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:09.599557+00:00
-- url     : https://prove2.me/theorems/10cf13a1-0d73-4e89-836d-1291178b0d16
-- title:
--   Separable polynomial $s(x)=\sum_{i=1}^n s_i(x_i)$
-- statement:
--   A real polynomial $s$ in the variables $x_1,\dots,x_n$ is **separable** if there are univariate real polynomials $s_1,\dots,s_n$ with
--   $$
--   s(x)=\sum_{i=1}^n s_i(x_i).
--   $$
--   So every monomial of $s$ involves at most one variable. Separable polynomials are the first summand in the definition of SPQ polynomials (Definition 1).
--
--   **Formalization Note** Polynomials in $n$ variables are `MvPolynomial (Fin n) ℝ`, and the paper's $x_i$ is `X (i-1)`. Each $s_i$ is a univariate `Polynomial ℝ`, substituted at the single variable `X i` with `Polynomial.aeval`, so it cannot mix variables.
-- source:
--   Ahmadi, Dibek & Hall, Sums of Separable and Quadratic Polynomials, arXiv:2105.04766v1, Definition 1, p.1

import Mathlib

open MvPolynomial

namespace SPQPoly

/-- **Separable polynomial.**
Ahmadi, Dibek & Hall, *Sums of Separable and Quadratic Polynomials*, arXiv:2105.04766v1,
Definition 1, p.1: "s(x) is a separable polynomial, i.e., s(x) = Σ_{i=1}^n s_i(x_i) for some
univariate polynomials s_i : R → R".

A polynomial `s` in the variables `x₀, …, x_{n-1}` is separable if it is a sum
`Σᵢ uᵢ(xᵢ)` of univariate real polynomials `uᵢ`, the `i`-th one evaluated at the `i`-th variable.

**Formalization Note.** Polynomials in `n` variables are `MvPolynomial (Fin n) ℝ`; the paper's
`x₁, …, xₙ` are `X 0, …, X (n-1)`. Each `uᵢ` is a univariate `Polynomial ℝ`, substituted at
`X i` by `Polynomial.aeval`; it cannot mix variables. -/
def IsSeparable {n : ℕ} (s : MvPolynomial (Fin n) ℝ) : Prop :=
  ∃ u : Fin n → Polynomial ℝ, s = ∑ i, Polynomial.aeval (X i : MvPolynomial (Fin n) ℝ) (u i)

end SPQPoly


