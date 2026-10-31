-- Prove2me | Definitions.Def_SPQPoly_p32
-- name    : SPQPoly_p32
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:11.706168+00:00
-- url     : https://prove2.me/theorems/02127251-87f9-4bd9-a727-3243ce78249f
-- title:
--   The bivariate sextic of Theorem 3.2
-- statement:
--   The polynomial in $x=(x_1,x_2)$
--   $$
--   p(x)=17x_1^6-20x_1^4+7x_1^2+18x_1+18x_2^4-19x_2^2-19x_2+21-20x_1x_2 .
--   $$
--   Its only mixed term is $-20x_1x_2$, of degree $2$, so it is SPQ. Theorem 3.2 shows that it is nonnegative but not a sum of squares.
--
--   **Formalization Note** $x_1,x_2$ are `X 0, X 1`; the coefficients are real constants `C c`.
-- source:
--   Ahmadi, Dibek & Hall, Sums of Separable and Quadratic Polynomials, arXiv:2105.04766v1, Theorem 3.2, p.9

import Mathlib

open MvPolynomial

namespace SPQPoly

/-- **The bivariate sextic of Theorem 3.2.**
Ahmadi, Dibek & Hall, *Sums of Separable and Quadratic Polynomials*, arXiv:2105.04766v1,
Theorem 3.2, p.9: "p(x) = 17x1^6 − 20x1^4 + 7x1^2 + 18x1 + 18x2^4 − 19x2^2 − 19x2 + 21 − 20x1x2".

**Formalization Note.** `x₁ = X 0`, `x₂ = X 1`; the terms are in the order printed. -/
noncomputable def p32 : MvPolynomial (Fin 2) ℝ :=
  C (17 : ℝ) * X 0 ^ 6 - C (20 : ℝ) * X 0 ^ 4 + C (7 : ℝ) * X 0 ^ 2 + C (18 : ℝ) * X 0
    + C (18 : ℝ) * X 1 ^ 4 - C (19 : ℝ) * X 1 ^ 2 - C (19 : ℝ) * X 1 + C (21 : ℝ)
    - C (20 : ℝ) * X 0 * X 1

end SPQPoly


