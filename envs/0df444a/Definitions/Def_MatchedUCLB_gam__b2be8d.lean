-- Prove2me | Definitions.Def_MatchedUCLB_gam__b2be8d
-- name    : MatchedUCLB_gam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:25.593226+00:00
-- url     : https://prove2.me/theorems/b2be8dd3-fb75-46ad-947f-bf1eaf45c9a2
-- title:
--   The inner radius parameter $\gamma=\theta\sqrt{3a_0/(32a_1)}$
-- statement:
--   For the matched order $q=p+\nu$ (with $p\ge2$, $0<\nu\le1$), the construction uses the constant
--
--   $$
--   \gamma=\theta\sqrt{\frac{3a_0}{32a_1}} .
--   $$
--
--   It depends only on $q$, hence only on $p$ and $\nu$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eq. (4.6), p.6

import Mathlib
import Definitions.Def_MatchedUCLB_theta
import Definitions.Def_MatchedUCLB_a1

namespace MatchedUCLB

/-- **The constant `γ = θ √(3a_0/(32a_1))` (the inner radius parameter).** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, (4.6), p.6. Here `q = p + ν`.

**Formalization Note.** `q` is a real parameter; every power with exponent depending on `q` is
`Real.rpow`. The constant depends on `q` only. -/
noncomputable def gam (q : ℝ) : ℝ :=
  theta q * Real.sqrt (3 * a0 q / (32 * a1 q))

end MatchedUCLB


