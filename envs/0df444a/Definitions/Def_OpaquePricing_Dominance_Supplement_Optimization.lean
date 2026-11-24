-- Prove2me | Definitions.Def_OpaquePricing_Dominance_Supplement_Optimization
-- name    : OpaquePricing_Dominance_Supplement_Optimization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:32:08.258804+00:00
-- url     : https://prove2.me/theorems/47c03692-163b-45f5-9713-74005a41ed3e
-- title:
--   The six-variable ratio optimization OPT in display (12)
-- statement:
--   Let $N\ge2$. A feasible point consists of real numbers $x,y,a,b,c,d$ satisfying $a,b,c,d\ge0$, $a+b+c+d=1$ and $x\ge y\ge x/N\ge0$. Set
--   $$D=\max\{x(a+b),y(a+b+c)\},\qquad OPT_N=\sup_{D>0}\frac{xa+y(b+c)}{D}.$$
--   Lemma 8 also concludes that this supremum is attained, preserving the source maximum. The supremum ranges over the entire feasible domain of display (12), with no presumed optimizer and no price normalization. Zero-denominator cases have zero numerator and zero revenue and are omitted from the ratio supremum. The supremum is in $[0,\infty]$, so an unbounded domain never silently receives a real default value.
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Appendix I.7, pp. 50–51, display (12); Appendix J, pp. 53–54

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

/-- Display (12), without a positivity assumption on the prices or probabilities. -/
structure RatioPoint (N : ℕ) where
  x : ℝ
  y : ℝ
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  a_nonneg : 0 ≤ a
  b_nonneg : 0 ≤ b
  c_nonneg : 0 ≤ c
  d_nonneg : 0 ≤ d
  total : a + b + c + d = 1
  y_le_x : y ≤ x
  lower : x / N ≤ y
  x_nonneg : 0 ≤ x / N

noncomputable def ratioDen {N : ℕ} (z : RatioPoint N) : ℝ :=
  max (z.x * (z.a + z.b)) (z.y * (z.a + z.b + z.c))

noncomputable def ratioValue {N : ℕ} (z : RatioPoint N) : ℝ :=
  (z.x * z.a + z.y * (z.b + z.c)) / ratioDen z

/-- The positive-denominator supremum; omitted zero denominators have zero revenue. -/
noncomputable def optRatio (N : ℕ) : ENNReal :=
  ⨆ (z : RatioPoint N) (_ : 0 < ratioDen z), ENNReal.ofReal (ratioValue z)

end OpaquePricing.Dominance.Supplement


