-- Prove2me | Definitions.Def_SinglePointPricing_Det_Supplement_IntervalFamily
-- name    : SinglePointPricing_Det_Supplement_IntervalFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T17:29:51.663513+00:00
-- url     : https://prove2.me/theorems/4b332fd9-0a53-43dd-a80c-cd09223b157d
-- title:
--   Display (F-1) — endpoint-data worst-case family under interval information
-- statement:
--   For $w>0$, $\alpha\in[0,1]$, and $0<q_l\le q_h<1$, use the published truncated generalized Pareto family $F_\alpha(\cdot\mid r,(w,q))$ and the lower and upper parameter endpoints $\underline r_\alpha(w,q)$ and $\overline r_\alpha(w,q)$. Define
--   $$
--   \mathcal S_{\alpha,w,q_l,q_h}=
--   \{F_\alpha(\cdot\mid r,(w,q_l)):r\in[\underline r_\alpha(w,q_l),w)\}
--   \cup
--   \{F_\alpha(\cdot\mid r,(w,q_h)):r\in[w,\overline r_\alpha(w,q_h)]\}.
--   $$
--   The second family is empty when its upper endpoint is below $w$. Its upper-bound test is written $\alpha\Gamma_\alpha^{-1}(q_h)r\le w$, so at $\alpha=0$ all finite $r\ge w$ are allowed. Members are probability measures supported on nonnegative values whose closed tail is the stated function. This is the family in the interval-information fundamental reduction.
-- source:
--   Allouah, Bahamou & Besbes, Optimal Pricing with a Single Point, arXiv:2103.05611v2, (F-1), p. App-39 and top of p. App-40

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Supplement_Interval

namespace SinglePointPricing.Det.Supplement

open MeasureTheory

/-- (F-1), App-39: the union of the two endpoint-data families. The high family
is empty if the upper parameter bound is below `w`; no spurious real infinity. -/
def SFamilyI (α w ql qh : ℝ) : Set (Measure ℝ) :=
  {μ | IsProbabilityMeasure μ ∧ μ (Set.Iio 0) = 0 ∧
    ((∃ r ∈ Set.Ico (rLow α w ql) w,
        ∀ v : ℝ, 0 ≤ v → sf μ v = Fbar α w ql r v) ∨
     (∃ r : ℝ, w ≤ r ∧ α * GammaAInv α qh * r ≤ w ∧
        ∀ v : ℝ, 0 ≤ v → sf μ v = Fbar α w qh r v))}

end SinglePointPricing.Det.Supplement


