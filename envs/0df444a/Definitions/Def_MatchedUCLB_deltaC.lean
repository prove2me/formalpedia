-- Prove2me | Definitions.Def_MatchedUCLB_deltaC
-- name    : MatchedUCLB_deltaC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:23.314211+00:00
-- url     : https://prove2.me/theorems/7cb47b45-f36d-4082-81cf-16826807e4a2
-- title:
--   The smoothing width $\delta_j=c_1\lambda m\tau_j^q$
-- statement:
--   For $\lambda>0$, a chain length $m$ and a scale $\tau$, the **smoothing width** of the phase is $\delta=c_1\lambda m\tau^q$, with $c_1=2^{-q-3}/q$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Sec. 4.3, p.8; Lemma 4.5(c), p.10

import Mathlib
import Definitions.Def_MatchedUCLB_c1

namespace MatchedUCLB

/-- **The smoothing width `δ_j = c_1 λ m τ_j^q`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Sec. 4.3, p.8 ("we choose
`δ_j = c_1 λ m τ_j^q`, with `c_0 = c_1 = 2^{−q−3}/q`"), and Lemma 4.5(c), p.10. -/
noncomputable def deltaC (q : ℝ) (m : ℕ) (lam τ : ℝ) : ℝ :=
  c1 q * lam * m * τ ^ q

end MatchedUCLB


