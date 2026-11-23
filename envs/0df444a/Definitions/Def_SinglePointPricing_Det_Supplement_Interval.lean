-- Prove2me | Definitions.Def_SinglePointPricing_Det_Supplement_Interval
-- name    : SinglePointPricing_Det_Supplement_Interval
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T17:29:20.568896+00:00
-- url     : https://prove2.me/theorems/d2e913c3-941d-48b2-ab91-0fe4aca0e118
-- title:
--   §2 and §6 — α-strongly regular value laws with interval conversion information
-- statement:
--   Fix $w>0$, $\alpha\in[0,1]$ and $0<q_l\le q_h<1$. The seller knows only that the conversion rate at $w$ belongs to $[q_l,q_h]$. The admissible class is
--   $$
--   \mathcal F_\alpha(w,[q_l,q_h])=
--   \{F\in\mathcal G:F\text{ is }\alpha\text{-strongly regular},\ q_l\le\overline F(w)\le q_h\}.
--   $$
--   The reused class $\mathcal G$ consists of nonnegative value laws with finite positive mean. Strong regularity and the closed tail $\overline F(v)=\Pr[V\ge v]$ are the published base definitions, including a possible atom at the top of the support. This definition supplies interval information without imposing any new condition on the value laws.
-- source:
--   Allouah, Bahamou & Besbes, Optimal Pricing with a Single Point, arXiv:2103.05611v2, §2, p. 11; §6, p. 30

import Mathlib
import Definitions.Def_SinglePointPricing_Det_WorstCase

namespace SinglePointPricing.Det.Supplement

open MeasureTheory

/-- §2, p. 11 and §6, p. 30: the interval information class. -/
def FClassI (α w ql qh : ℝ) : Set (Measure ℝ) :=
  {μ | InG μ ∧ IsAlphaSR α μ ∧ sf μ w ∈ Set.Icc ql qh}

end SinglePointPricing.Det.Supplement


