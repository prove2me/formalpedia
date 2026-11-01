-- Prove2me | Definitions.Def_MaxWeightInstab_horizon
-- name    : MaxWeightInstab_horizon
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:35.790062+00:00
-- url     : https://prove2.me/theorems/e33d673f-c7ee-44cc-84e1-f2b0a103dc4b
-- title:
--   Time horizon $T$ of display (14)
-- statement:
--   $$
--   T=\frac{2M}{(1-a)(1-r_{\boldsymbol\rho})} .
--   $$
--
--   The page prints $T=2M/(1-a)(1-r_{\boldsymbol\rho})$; the product is the denominator, as the proof of Lemma 2 (p.9) confirms.
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, display (14), p.6

import Mathlib
import Definitions.Def_MaxWeightInstab_rRho

namespace MaxWeightInstab

/-- The time horizon `T = 2M/(1 − a)(1 − r_ρ)`, display (14) (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, p.6), read as
`T = 2M/((1 − a)(1 − r_ρ))` (the proof of Lemma 2, p.9, uses `U ≤ 2M/(1 − r_ρ) < T`). -/
noncomputable def horizon (a : ℝ) (ν : ℕ) (M : ℝ) : ℝ :=
  2 * M / ((1 - a) * (1 - rRho a ν))

end MaxWeightInstab


