-- Prove2me | Definitions.Def_KSPolySign_IsRatC
-- name    : KSPolySign_IsRatC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:28:36.16968+00:00
-- url     : https://prove2.me/theorems/264af1cf-ff85-4244-b8fd-24dafafd5897
-- title:
--   Rational complex numbers
-- statement:
--   A complex number $z$ is **rational** when both its real part and its imaginary part are rational numbers. A complex matrix is rational when every entry is.
--
--   This is the meaning of "rational inputs" in Theorem 6.8(b).
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Theorem 6.8(b), p.68 (PDF p.68)

import Mathlib
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Rational complex numbers.** A complex number is rational when its real part and its imaginary
part are rational. Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Theorem 6.8(b), p.68 (PDF p.68): "For rational inputs".

**Formalization Note** "Rational" for a complex matrix entry is read as: both the real and the
imaginary part are rational numbers. -/
def IsRatC (z : ℂ) : Prop := (∃ q : ℚ, z.re = q) ∧ ∃ q : ℚ, z.im = q

end KSPolySign


