-- Prove2me | Definitions.Def_FluidGreedyMatching_CliqueBomb_Supplement_Constants
-- name    : FluidGreedyMatching_CliqueBomb_Supplement_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:13:33.899125+00:00
-- url     : https://prove2.me/theorems/8988ea2e-7df4-4d76-bcfe-09b840f16b89
-- title:
--   The exact RDO, bipartite MRG and paw constants
-- statement:
--   For $\sigma>0$, put $w=\sqrt{\sigma/(2+\sigma)}$ and define
--   $$\rho_{\rm RDO}(\sigma)=\frac23-\frac23 w^3+w^4.$$
--   The bipartite MRG constant at $\sigma=5/4$ is the specialization of Eq. (5.3), normalized by $2+\sigma$:
--   $$
--   \rho_S=\frac4{13}\left[\int_1^{9/5}\left(\frac9{v^4}-\frac{5/2}{v^3}\right)e^{5(v-1)/9}\,dv+\frac54\left(\frac59\right)^4e^{8/9}\right].
--   $$
--   The integrand is continuous on the compact interval $[1,9/5]$, which excludes every pole. Finally, define
--   $$F(w)=\frac{2w^2+\tfrac12w^6+\tfrac23(1-w^3)}{3w^2+1}.$$
--   Its denominator is positive for every real $w$; Theorem 1.5 minimizes it on $(0,1)$.
--
--   These are explicit formulas, not definitions by stochastic limits or decimal approximations. They contain no numerical enclosure assumptions. The subsequent theorem items assert the corresponding limits and numerical bounds.
-- source:
--   Sayan Mukherjee, Fluid Limits and Upper Bounds for Randomized Greedy Matching, STOC 2027 submission #492 (October 2026), Theorem 1.2, p. 4; Proposition 4.3, Eq. (4.1), p. 18; §5.3, Eq. (5.3), and §5.4, p. 25

import Mathlib

set_option autoImplicit false

namespace FluidGreedyMatching.CliqueBomb.Supplement

noncomputable section

/-- Theorem 1.2, p. 4. Only σ>0 is used in the theorem. -/
def rhoRDO (σ : ℝ) : ℝ :=
  let w := Real.sqrt (σ / (2 + σ))
  2 / 3 - (2 / 3) * w ^ 3 + w ^ 4

/-- Eq. (5.3) at σ=5/4, divided by 2+σ=13/4.
The integrand is continuous on [1,9/5], so the interval integral is genuine. -/
def rhoS : ℝ :=
  ((∫ v in (1 : ℝ)..(9 / 5 : ℝ),
    (9 / v ^ 4 - (5 / 2) / v ^ 3) * Real.exp (5 * (v - 1) / 9)) +
    (5 / 4) * (5 / 9 : ℝ) ^ 4 * Real.exp (8 / 9)) / (13 / 4)

/-- Proposition 4.3, Eq. (4.1), p. 18. -/
def pawValue (w : ℝ) : ℝ :=
  (2 * w ^ 2 + (1 / 2) * w ^ 6 + (2 / 3) * (1 - w ^ 3)) / (3 * w ^ 2 + 1)

end
end FluidGreedyMatching.CliqueBomb.Supplement


