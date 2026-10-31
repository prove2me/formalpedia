-- Prove2me | Definitions.Def_SPQPoly_IsSPQ
-- name    : SPQPoly_IsSPQ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:37:10.377975+00:00
-- url     : https://prove2.me/theorems/5f4ee966-39f9-4027-ace0-f79a8e2c1f15
-- title:
--   Separable plus quadratic (SPQ) polynomial
-- statement:
--   A real polynomial $p$ in $n$ variables is **separable plus quadratic (SPQ)** if
--   $$
--   p(x)=s(x)+q(x),
--   $$
--   where $s$ is separable, i.e. $s(x)=\sum_{i=1}^n s_i(x_i)$ for univariate polynomials $s_i$, and $q$ is a quadratic polynomial, i.e. a polynomial of total degree at most $2$.
--
--   Equivalently, every monomial of $p$ that involves two or more variables has degree at most $2$. This is the class of polynomials the whole paper studies.
--
--   **Formalization Note** "Quadratic polynomial" means total degree at most $2$, constant and linear terms included; it is not required to be a quadratic form.
-- source:
--   Ahmadi, Dibek & Hall, Sums of Separable and Quadratic Polynomials, arXiv:2105.04766v1, Definition 1, p.1

import Mathlib
import Definitions.Def_SPQPoly_IsSeparable

open MvPolynomial

namespace SPQPoly

/-- **Separable plus quadratic (SPQ) polynomial.**
Ahmadi, Dibek & Hall, *Sums of Separable and Quadratic Polynomials*, arXiv:2105.04766v1,
Definition 1, p.1: "A polynomial p : Rn → R is separable plus quadratic (SPQ) if
p(x) = s(x)+q(x), where s(x) is a separable polynomial, i.e., s(x) = Σ_{i=1}^n s_i(x_i) for some
univariate polynomials s_i : R → R, and q(x) is a quadratic polynomial."

**Formalization Note.** "Quadratic polynomial" is a polynomial of total degree at most `2`
(constant and linear terms included; it is not required to be a quadratic form). -/
def IsSPQ {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∃ s q : MvPolynomial (Fin n) ℝ, IsSeparable s ∧ q.totalDegree ≤ 2 ∧ p = s + q

end SPQPoly


