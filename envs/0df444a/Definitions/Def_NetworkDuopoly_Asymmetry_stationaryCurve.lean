-- Prove2me | Definitions.Def_NetworkDuopoly_Asymmetry_stationaryCurve
-- name    : NetworkDuopoly_Asymmetry_stationaryCurve
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:18:20.897371+00:00
-- url     : https://prove2.me/theorems/1b1c3d20-be37-4680-ba57-554d0b0d63d0
-- title:
--   The logarithmic map, its Lambert W inverse, and the stationary-response curve
-- statement:
--   For $t>0$ let $h(t)=t+\log t$. For real $s$ define $H(s)=W(e^s)$ using the principal real Lambert function. For real quality $\alpha$, strength $\gamma$, and $x\ge0$, define
--   $$
--   \bar y_{\alpha,\gamma}(x)=1-x-\frac{x}{H(\alpha-1+\gamma x)}.
--   $$
--   The curve expresses the inverse stationarity relation associated with equation (7). A point on this curve need not give a global best response. Lemma EC.1 establishes that $H$ is positive and is the inverse of $h$ on the positive half-line, together with the curvature and derivative properties needed for the mission.
--
--   **Formalization Note** The published function $W(a)$ chooses a real $w\ge-1$ with $we^w=a$ when such a root exists and otherwise returns zero. No positivity or inverse identity is assumed by the definitions; those facts are conclusions of the lemma. The Lean functions $h,H,\bar y$ are total on $\mathbb R$. Only $t>0$ is the intended domain of $h$; curve assertions use $x\ge0$. The reused advance-sales model's other definitions play no role here.
-- source:
--   Chen and Chen (2021), Duopoly Competition with Network Effects in Discrete Choice Models, https://doi.org/10.1287/opre.2020.2079; supplied artifact p. 16 (PDF 16), Definition 1 and footnote 6; pp. ec3–ec4 (PDF 47–48), Lemma EC.1.

import Definitions.Def_AdvanceSales_Pricing_Setting

namespace NetworkDuopoly.Asymmetry

/- Imported declaration bodies (verbatim), included for standalone audit.
namespace AdvanceSales.Pricing
noncomputable def lambertW (a : ℝ) : ℝ :=
  by classical exact if h : ∃ w : ℝ, -1 ≤ w ∧ w * Real.exp w = a then Classical.choose h else 0
end AdvanceSales.Pricing
-/

noncomputable def h (t : ℝ) : ℝ := t + Real.log t

noncomputable def H (t : ℝ) : ℝ := AdvanceSales.Pricing.lambertW (Real.exp t)

noncomputable def stationaryCurve (α γ x : ℝ) : ℝ :=
  1 - x - x / H (α - 1 + γ * x)

end NetworkDuopoly.Asymmetry


