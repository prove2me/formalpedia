-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch09_ch09Lambda
-- name    : RamanujanLostNotebook_PartII_ch09_ch09Lambda
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T11:09:03.404127+00:00
-- url     : https://prove2.me/theorems/dc20e845-ff68-486e-86c6-4f923a6ace5f
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 9: ch09Lambda
-- statement:
--   Cubic invariant λₙ from the unambiguous Euler quotient (9.1.4), p.196:
--   q=exp(−π√(n/3)), λₙ=q^(−1/2)(f(q)/f(q³))⁶/(3√3).
--   The exponential implements the positive square-root branch. The ellipsis
--   in (9.1.1), p.195, is thus completed by factors 1−(−q)^k for k≥1, 3∤k.
--   It must not be extended as just (1+q)∏_{k≥1}(1−q^(2k)).
--   Every statement returns convergence and nonzero-product conditions through
--   the λₙ regularity predicate (n>0, convergent nonzero Euler products at −q and −q³, λₙ>0); n≤0 is outside the source domain.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 9.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch09_ch09F
import Definitions.Def_RamanujanLostNotebook_PartII_ch09_ch09Nome

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Cubic invariant λₙ from the unambiguous Euler quotient (9.1.4), p.196:
q=exp(−π√(n/3)), λₙ=q^(−1/2)(f(q)/f(q³))⁶/(3√3).
The exponential implements the positive square-root branch. The ellipsis
in (9.1.1), p.195, is thus completed by factors 1−(−q)^k for k≥1, 3∤k.
It must not be extended as just (1+q)∏_{k≥1}(1−q^(2k)).
Every statement returns convergence and nonzero-product conditions through
the λₙ regularity predicate (n>0, convergent nonzero Euler products at −q and −q³, λₙ>0); n≤0 is outside the source domain. -/
noncomputable def ch09Lambda (n : ℝ) : ℝ :=
  Real.exp (Real.pi * Real.sqrt (n / 3) / 2) / (3 * Real.sqrt 3) *
    (ch09F (ch09Nome n) / ch09F (ch09Nome n ^ 3)) ^ 6

end RamanujanLostNotebook.PartII

end


