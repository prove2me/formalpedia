-- Prove2me | Definitions.Def_MatchedUCLB_theta
-- name    : MatchedUCLB_theta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:17.126221+00:00
-- url     : https://prove2.me/theorems/37147c0a-2b8a-4c04-81ef-1199ff6c0ba6
-- title:
--   The radius parameter $\theta=\min\{1/16,(3qa_0/32)^{1/(q-2)}\}$
-- statement:
--   For the matched order $q=p+\nu$ (with $p\ge2$, $0<\nu\le1$), the construction uses the constant
--
--   $$
--   \theta=\min\Bigl\{\frac1{16},\Bigl(\frac{3qa_0}{32}\Bigr)^{\frac1{q-2}}\Bigr\} .
--   $$
--
--   It depends only on $q$, hence only on $p$ and $\nu$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eq. (4.6), p.6

import Mathlib
import Definitions.Def_MatchedUCLB_a0

namespace MatchedUCLB

/-- **The constant `θ = min{1/16, (3qa_0/32)^{1/(q−2)}}`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, (4.6), p.6. Here `q = p + ν`.

**Formalization Note.** `q` is a real parameter; every power with exponent depending on `q` is
`Real.rpow`. The constant depends on `q` only. -/
noncomputable def theta (q : ℝ) : ℝ :=
  min (1 / 16) ((3 * q * a0 q / 32) ^ (1 / (q - 2)))

end MatchedUCLB


