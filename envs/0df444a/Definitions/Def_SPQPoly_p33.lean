-- Prove2me | Definitions.Def_SPQPoly_p33
-- name    : SPQPoly_p33
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:11.780653+00:00
-- url     : https://prove2.me/theorems/b6775438-3fb4-4bfc-a541-6855a42aaca8
-- title:
--   The trivariate quartic of Theorem 3.3
-- statement:
--   The polynomial in $x=(x_1,x_2,x_3)$
--   $$
--   p(x)=x_1^4+2x_1^2+x_2^4+2x_2^2+x_3^4+2x_3^2+\frac94+8x_1x_2+8x_1x_3+8x_2x_3 .
--   $$
--   Its mixed terms all have degree $2$, so it is SPQ. Theorem 3.3 shows that it is nonnegative but not a sum of squares.
--
--   **Formalization Note** $x_1,x_2,x_3$ are `X 0, X 1, X 2`; the constant term is the real number $9/4$.
-- source:
--   Ahmadi, Dibek & Hall, Sums of Separable and Quadratic Polynomials, arXiv:2105.04766v1, Theorem 3.3, p.9

import Mathlib

open MvPolynomial

namespace SPQPoly

/-- **The trivariate quartic of Theorem 3.3.**
Ahmadi, Dibek & Hall, *Sums of Separable and Quadratic Polynomials*, arXiv:2105.04766v1,
Theorem 3.3, p.9: "p(x) = x1^4 + 2x1^2 + x2^4 + 2x2^2 + x3^4 + 2x3^2 + 9/4 + 8x1x2 + 8x1x3 + 8x2x3".

**Formalization Note.** `x₁ = X 0`, `x₂ = X 1`, `x₃ = X 2`; the constant term is the real
number `9/4`; the terms are in the order printed. -/
noncomputable def p33 : MvPolynomial (Fin 3) ℝ :=
  X 0 ^ 4 + C (2 : ℝ) * X 0 ^ 2 + X 1 ^ 4 + C (2 : ℝ) * X 1 ^ 2 + X 2 ^ 4 + C (2 : ℝ) * X 2 ^ 2
    + C (9 / 4 : ℝ) + C (8 : ℝ) * X 0 * X 1 + C (8 : ℝ) * X 0 * X 2 + C (8 : ℝ) * X 1 * X 2

end SPQPoly


