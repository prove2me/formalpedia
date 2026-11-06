-- Prove2me | Definitions.Def_MatchedUCLB_a1
-- name    : MatchedUCLB_a1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:30.738923+00:00
-- url     : https://prove2.me/theorems/7ef5b33d-d1e1-4c58-ad9c-91baad2c7957
-- title:
--   The constant $a_1=\tfrac{q-1}{2}(5/4)^{q-2}$
-- statement:
--   For the matched order $q=p+\nu$ (with $p\ge2$, $0<\nu\le1$), the construction uses the constant
--
--   $$
--   a_1=\frac{q-1}{2}\Bigl(\frac54\Bigr)^{q-2} .
--   $$
--
--   It depends only on $q$, hence only on $p$ and $\nu$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eq. (4.6), p.6

import Mathlib

namespace MatchedUCLB

/-- **The constant `a_1 = ((q−1)/2) (5/4)^{q−2}`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, (4.6), p.6. Here `q = p + ν`.

**Formalization Note.** `q` is a real parameter; every power with exponent depending on `q` is
`Real.rpow`. The constant depends on `q` only. -/
noncomputable def a1 (q : ℝ) : ℝ :=
  (q - 1) / 2 * (5 / 4 : ℝ) ^ (q - 2)

end MatchedUCLB


