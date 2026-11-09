-- Prove2me | Definitions.Def_SelectiveDPT_zeta
-- name    : SelectiveDPT_zeta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:48:55.202834+00:00
-- url     : https://prove2.me/theorems/125f83a2-5f7a-40d2-9521-a5179e491cc4
-- title:
--   Conversion loss $\zeta(\varepsilon)$
-- statement:
--   The **conversion loss** of Theorem 3.1 is
--   $$\zeta(\varepsilon) = \frac{1 - 2\sqrt{\varepsilon(1-\varepsilon)}}{\ln\!\big(1 - (1 - (2(1-\varepsilon))^{1/3})^3\big)} .$$
--   On $[0, 1/3]$ it is positive and below $58$ (Theorem 3.1); it is the factor lost when a negative-weights adversary bound is converted into a multiplicative one.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Theorem 3.1 part 3, p.18

import Mathlib

namespace SelectiveDPT

/-- The conversion loss `ζ(ε) = (1 − 2√(ε(1 − ε))) / ln(1 − (1 − (2(1 − ε))^{1/3})³)` of
Theorem 3.1 (arXiv:2609.26678, Theorem 3.1 part 3, p.18). -/
noncomputable def zeta (ε : ℝ) : ℝ :=
  (1 - 2 * Real.sqrt (ε * (1 - ε))) /
    Real.log (1 - (1 - (2 * (1 - ε)) ^ ((1 : ℝ) / 3)) ^ 3)

end SelectiveDPT


