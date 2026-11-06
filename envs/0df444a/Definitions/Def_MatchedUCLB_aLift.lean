-- Prove2me | Definitions.Def_MatchedUCLB_aLift
-- name    : MatchedUCLB_aLift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:23.55521+00:00
-- url     : https://prove2.me/theorems/fb0f0e00-94b2-419c-a2d4-58bf3c892ef2
-- title:
--   The constant $a_{\mathrm{lift}}=a_0/8$
-- statement:
--   For the matched order $q=p+\nu$ (with $p\ge2$, $0<\nu\le1$), the construction uses the constant
--
--   $$
--   a_{\mathrm{lift}}=\frac{a_0}{8} .
--   $$
--
--   It depends only on $q$, hence only on $p$ and $\nu$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eq. (4.6), p.6

import Mathlib
import Definitions.Def_MatchedUCLB_a0

namespace MatchedUCLB

/-- **The constant `a_lift = a_0/8`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, (4.6), p.6. Here `q = p + ν`.

**Formalization Note.** `q` is a real parameter; every power with exponent depending on `q` is
`Real.rpow`. The constant depends on `q` only. -/
noncomputable def aLift (q : ℝ) : ℝ :=
  a0 q / 8

end MatchedUCLB


