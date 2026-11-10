-- Prove2me | Definitions.Def_EvasivePatterns_l1Norm
-- name    : EvasivePatterns_l1Norm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:13.34423+00:00
-- url     : https://prove2.me/theorems/31d07e8d-f856-43e2-9c94-f2034fed9a40
-- title:
--   The norm $\|A\|_1$ of an integer polynomial
-- statement:
--   For an integer polynomial $A(z) = \sum_i a_i z^i$, the norm $\|A\|_1 = \sum_i |a_i|$ is the sum of the absolute values of its coefficients. It appears in the full-norm identity $\|Q_P Q_P^*\|_1 = |S_P|^2$.
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), §2, p.3 (PDF p.4), line 102

import Mathlib

namespace EvasivePatterns

/-- **The norm `‖A‖₁`** of an integer polynomial: the sum of the absolute values of its
coefficients.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), §2, printed p. 3 (PDF p. 4), line 102: "Here ∥·∥_1 is the sum of
absolute values of the coefficients." -/
def l1Norm (A : Polynomial ℤ) : ℤ :=
  ∑ i ∈ A.support, |A.coeff i|

end EvasivePatterns


