-- Prove2me | Definitions.Def_MatchedUCLB_eta
-- name    : MatchedUCLB_eta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:28.334047+00:00
-- url     : https://prove2.me/theorems/5e6c9a4f-be40-4a15-ad89-a305e3df42a9
-- title:
--   The contraction factor $\eta=\gamma/(2(1+\theta))$
-- statement:
--   For the matched order $q=p+\nu$ (with $p\ge2$, $0<\nu\le1$), the construction uses the constant
--
--   $$
--   \eta=\frac{\gamma}{2(1+\theta)} .
--   $$
--
--   It depends only on $q$, hence only on $p$ and $\nu$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Lemma 4.5, p.10; Step 1.4, p.6

import Mathlib
import Definitions.Def_MatchedUCLB_gam__b2be8d
import Definitions.Def_MatchedUCLB_theta

namespace MatchedUCLB

/-- **The constant `η = γ/(2(1+θ))`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Lemma 4.5, p.10 (and Lemma 4.3, Step 1.4, p.6). Here `q = p + ν`.

**Formalization Note.** `q` is a real parameter; every power with exponent depending on `q` is
`Real.rpow`. The constant depends on `q` only. -/
noncomputable def eta (q : ℝ) : ℝ :=
  gam q / (2 * (1 + theta q))

end MatchedUCLB


