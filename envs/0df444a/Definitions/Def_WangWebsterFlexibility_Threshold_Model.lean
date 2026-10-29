-- Prove2me | Definitions.Def_WangWebsterFlexibility_Threshold_Model
-- name    : WangWebsterFlexibility_Threshold_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:32:44.644307+00:00
-- url     : https://prove2.me/theorems/bbe0e002-8fe6-4a5b-8f37-3c15365bb4b6
-- title:
--   Independent demand laws and priority allocations
-- statement:
--   Let $D_1,D_2$ have arbitrary independent Borel probability distributions on $[0,\infty)$. A model consists of these two laws, the product margins $\pi_1,\pi_2$, and the primary failure parameter $\rho$. The economic inequalities are imposed by the theorem statements. The joint law is the product of the two laws and expectation is integration against that product.
--
--   Write $x^+=\max(0,x)$. Given demands $d_1,d_2$, dedicated available primary quantities $a_1,a_2$, and backup capacity $s$, define $x_i=\min(d_i,a_i)$, $r_i=(d_i-a_i)^+$, $y_1=\min(r_1,s)$ and $y_2=\min(r_2,(s-r_1)^+)$. Then $R=\pi_1x_1+\pi_2x_2+(\pi_1-v)y_1+(\pi_2-v)y_2$.
--
--   For a successful flexible primary with capacity $q$, define $X_1=\min(d_1,q)$, $X_2=\min(d_2,(q-d_1)^+)$, $Y_1=\min((d_1-q)^+,s)$ and $Y_2=\min((d_2-(q-d_1)^+)^+,(s-(d_1-q)^+)^+)$. Its revenue net of exercise charges is $R_{ff}=\pi_1X_1+\pi_2X_2+(\pi_1-v)Y_1+(\pi_2-v)Y_2$.
--
--   These are the source's product-1-first allocations, not an optimization over allocation policies. For feasible finite decisions all sales are bounded measurable functions, so no finite demand moment is needed. The generic expectation operator uses the usual Bochner integral; arbitrary nonintegrable inputs to that generic operator return its total-function default, but the sales functions used in this mission are integrable.
-- source:
--   Wang and Webster (2021), Product Flexibility Strategy Under Supply and Demand Risk, Manufacturing & Service Operations Management, https://doi.org/10.1287/msom.2021.1037, §3, printed/PDF pp. 9–13, equations (4)–(5)

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

open scoped NNReal

namespace WangWebsterFlexibility.Threshold

/-- Two independent nonnegative demand laws and the common economic primitives (§3, pp. 9–11).
The laws are unrestricted Borel probability measures; no moment or density is assumed. -/
structure Model where
  demand₁ : ProbabilityMeasure ℝ≥0
  demand₂ : ProbabilityMeasure ℝ≥0
  π₁ : ℝ
  π₂ : ℝ
  ρ : ℝ

/-- Independence is implemented with the standard product measure. -/
noncomputable def Model.law (M : Model) : Measure (ℝ≥0 × ℝ≥0) :=
  (M.demand₁ : Measure ℝ≥0).prod (M.demand₂ : Measure ℝ≥0)

/-- Expected value under the independent demand laws. The sales expressions used below are
measurable and bounded for each fixed finite decision, even when demand has infinite mean. -/
noncomputable def Model.expect (M : Model) (f : ℝ≥0 × ℝ≥0 → ℝ) : ℝ :=
  ∫ d, f d ∂M.law

/-- Real positive part, used in the printed allocation formulas. -/
noncomputable def pos (x : ℝ) : ℝ := max 0 x

/-- Revenue net of exercise charges with dedicated available primary quantities (4), p. 12. -/
noncomputable def revenueDF (M : Model) (v : ℝ) (d : ℝ≥0 × ℝ≥0)
    (a₁ a₂ s : ℝ) : ℝ :=
  M.π₁ * min (d.1 : ℝ) a₁ + M.π₂ * min (d.2 : ℝ) a₂ +
    (M.π₁ - v) * min (pos ((d.1 : ℝ) - a₁)) s +
    (M.π₂ - v) * min (pos ((d.2 : ℝ) - a₂)) (pos (s - pos ((d.1 : ℝ) - a₁)))

/-- Revenue net of exercise charges when the flexible primary succeeds (5), p. 13. -/
noncomputable def revenueFF (M : Model) (v : ℝ) (d : ℝ≥0 × ℝ≥0)
    (q s : ℝ) : ℝ :=
  M.π₁ * min (d.1 : ℝ) q + M.π₂ * min (d.2 : ℝ) (pos (q - (d.1 : ℝ))) +
    (M.π₁ - v) * min (pos ((d.1 : ℝ) - q)) s +
    (M.π₂ - v) * min (pos ((d.2 : ℝ) - pos (q - (d.1 : ℝ))))
      (pos (s - pos ((d.1 : ℝ) - q)))

end WangWebsterFlexibility.Threshold


