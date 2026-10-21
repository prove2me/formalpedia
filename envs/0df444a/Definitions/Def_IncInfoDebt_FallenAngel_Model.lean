-- Prove2me | Definitions.Def_IncInfoDebt_FallenAngel_Model
-- name    : IncInfoDebt_FallenAngel_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:34.661974+00:00
-- url     : https://prove2.me/theorems/082e9a77-9ef4-4b7d-9ad1-f7deb925828f
-- title:
--   Regime 4 killed transition law, conditional density, and hazard quotient
-- statement:
--   Let the log distance to default have drift $m\in\mathbb R$, volatility $\sigma>0$, and a positive observation lag $L$. The standard normal CDF is $N$. For $x,y,h>0$, the free Gaussian transition density is
--
--   $$g_h(x,y)=\frac{1}{\sqrt{2\pi\sigma^2h}}\exp\!\left[-\frac{(y-x-mh)^2}{2\sigma^2h}\right].$$
--
--   The density killed at zero is $K_h(x,y)=\mathbf1_{\{x>0,y>0\}}[g_h(x,y)-e^{-2xm/\sigma^2}g_h(-x,y)]$. Its survival probability and the Regime 4 conditional density, for a lagged state $a>0$, are
--
--   $$S_h(x)=\mathbf1_{\{x>0\}}\left[N\!\left(\frac{x+mh}{\sqrt{\sigma^2h}}\right)-e^{-2xm/\sigma^2}N\!\left(\frac{-x+mh}{\sqrt{\sigma^2h}}\right)\right],\qquad p_4(y\mid a)=\frac{K_L(a,y)}{S_L(a)}.$$
--
--   The short-horizon hazard quotient is $H_h(a)=h^{-1}\int_0^\infty(1-S_h(y))p_4(y\mid a)\,dy$; its positive-side limit defines the intensity. These formulas specify the reusable transition and observation model for the theorem targets.
--
--   **Formalization Note** The Brownian motion with drift is represented by these explicit transition laws, which the paper takes from Harrison (1985, Proposition 8.1); no Brownian sample-path structure is formalized. The definitions are total in Lean, while the theorems use $\sigma,L,a>0$ and $h\downarrow0$ to avoid default values at invalid inputs.
-- source:
--   Benzoni, Garlappi & Goldstein, Asymmetric Information, Dynamic Debt Issuance, and the Term Structure of Credit Spreads, Federal Reserve Bank of Chicago WP 2019-08 (20 Sept 2019; published as Incomplete Information, Debt Issuance, and the Term Structure of Credit Spreads, Management Science 2023, doi:10.1287/mnsc.2022.4529), pp. 13–16, (23)–(27); Online Appendix pp. 11–12, 16–18, (D.1)–(D.3), (D.19)–(D.20), https://doi.org/10.21033/wp-2019-08

import Mathlib
import Definitions.Def_BlackScholesModel_Core

namespace IncInfoDebt.FallenAngel
open MeasureTheory

/-- The standard normal cumulative distribution function used in (D.3). -/
noncomputable abbrev N (x : ℝ) : ℝ := BlackScholesModel.stdNormalCDF x

/-- Positive volatility and positive information lag; the drift remains unrestricted. -/
def Standing (σ L : ℝ) : Prop := 0 < σ ∧ 0 < L

/-- The free Gaussian transition density over a horizon `h`, from `x` to `y`. -/
noncomputable def freeDensity (σ m h x y : ℝ) : ℝ :=
  1 / Real.sqrt (2 * Real.pi * σ ^ 2 * h) *
    Real.exp (-(1 / (2 * σ ^ 2 * h)) * (y - x - m * h) ^ 2)

/-- The free solution minus the image solution in (D.2), before the indicators. -/
noncomputable def killedKernel (σ m h x y : ℝ) : ℝ :=
  freeDensity σ m h x y -
    Real.exp (-(2 * x * m / σ ^ 2)) * freeDensity σ m h (-x) y

/-- The numerator of (D.1), including both indicators in (D.2). -/
noncomputable def killedDensity (σ m h x y : ℝ) : ℝ :=
  if 0 < y ∧ 0 < x then killedKernel σ m h x y else 0

/-- The no-default probability over a horizon `h` from `x`, as in (D.3) and (D.17). -/
noncomputable def survival (σ m h x : ℝ) : ℝ :=
  if 0 < x then
    N ((x + m * h) / Real.sqrt (σ ^ 2 * h)) -
      Real.exp (-(2 * x * m / σ ^ 2)) *
        N ((-x + m * h) / Real.sqrt (σ ^ 2 * h))
  else 0

/-- The Regime 4 conditional density (D.1), conditional on the lagged state and survival. -/
noncomputable def condDensity (σ m L a y : ℝ) : ℝ :=
  killedDensity σ m L a y / survival σ m L a

/-- The final quotient in (D.19); its right limit defines the default intensity. -/
noncomputable def hazardQuotient (σ m L a h : ℝ) : ℝ :=
  (1 / h) * ∫ y in Set.Ioi (0 : ℝ),
    (1 - survival σ m h y) * condDensity σ m L a y

end IncInfoDebt.FallenAngel


