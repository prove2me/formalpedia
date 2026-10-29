-- Prove2me | Definitions.Def_WangWebsterFlexibility_Threshold_Profits
-- name    : WangWebsterFlexibility_Threshold_Profits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:33:04.359326+00:00
-- url     : https://prove2.me/theorems/2875d0f0-c49f-41e6-87f3-35b03c481aa2
-- title:
--   Expected profits and independently optimized values
-- statement:
--   For $s,q_1,q_2,q\ge0$, costs $c,\gamma,v$, and the allocations $R,R_{ff}$, define
--   $$u_{df}(s,q_1,q_2)=-\gamma s-c(1-\rho)(q_1+q_2)+\rho^2E[R(D;0,0,s)]+(1-\rho)^2E[R(D;q_1,q_2,s)]+\rho(1-\rho)E[R(D;q_1,0,s)]+\rho(1-\rho)E[R(D;0,q_2,s)],$$
--   $$u_{ff}(s,q)=-\gamma s-c(1-\rho)q+\rho E[R(D;0,0,s)]+(1-\rho)E[R_{ff}(D;q,s)].$$
--   Thus dedicated primary suppliers fail independently, while the consolidated primary has one common failure. Backup supply is reliable. Reservation is charged on all reserved capacity and primary cost on delivery, not on sales.
--
--   Define $U_{df}(c,\gamma,v)=\sup_{s,q_1,q_2\ge0}u_{df}(s,q_1,q_2)$ and $U_{ff}(c,\gamma,v)=\sup_{s,q\ge0}u_{ff}(s,q)$ in the extended reals. Each feasible set includes zero, and an unbounded objective gives $+\infty$. The two networks are optimized separately and no maximizer is assumed. An admissible fee at fixed $c,v$ means $\gamma\ge0$ and $\gamma+v>c$; the remaining economic inequalities are hypotheses of the theorems.
-- source:
--   Wang and Webster (2021), Product Flexibility Strategy Under Supply and Demand Risk, Manufacturing & Service Operations Management, https://doi.org/10.1287/msom.2021.1037, §3.3–3.4, printed/PDF pp. 12–13, equations (4)–(5); §4.3, p. 21

import Definitions.Def_WangWebsterFlexibility_Threshold_Model
import Mathlib.Data.EReal.Basic

open scoped NNReal

/- Imported definition bodies for the blind statement audit.
These are quotations of the imported Lean modules, not new declarations.

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

-/

namespace WangWebsterFlexibility.Threshold

/-- Equation (4): independent primary failures, reservation paid up front, primary paid
on delivery including unsold units. Decisions are all nonnegative finite real numbers.
There are FOUR weights: ρ², (1−ρ)², ρ(1−ρ), ρ(1−ρ). Their sum is one;
the last weight occurs twice, once for each different partial-failure state. -/
noncomputable def profitDF (M : Model) (c γ v : ℝ) (s q₁ q₂ : ℝ≥0) : ℝ :=
  -γ * (s : ℝ) - c * (1 - M.ρ) * ((q₁ : ℝ) + (q₂ : ℝ)) +
    M.ρ ^ 2 * M.expect (fun d => revenueDF M v d 0 0 s) +
    (1 - M.ρ) ^ 2 * M.expect (fun d => revenueDF M v d q₁ q₂ s) +
    M.ρ * (1 - M.ρ) * M.expect (fun d => revenueDF M v d q₁ 0 s) +
    M.ρ * (1 - M.ρ) * M.expect (fun d => revenueDF M v d 0 q₂ s)

/-- Equation (5): one common failure of the consolidated primary supplier. -/
noncomputable def profitFF (M : Model) (c γ v : ℝ) (s q : ℝ≥0) : ℝ :=
  -γ * (s : ℝ) - c * (1 - M.ρ) * (q : ℝ) +
    M.ρ * M.expect (fun d => revenueDF M v d 0 0 s) +
    (1 - M.ρ) * M.expect (fun d => revenueFF M v d q s)

/-- Independently optimized df value over the full feasible decision set, including zero.
The complete extended real order retains an unbounded supremum as positive infinity. -/
noncomputable def valueDF (M : Model) (c γ v : ℝ) : EReal :=
  ⨆ (s : ℝ≥0) (q₁ : ℝ≥0) (q₂ : ℝ≥0), (profitDF M c γ v s q₁ q₂ : EReal)

/-- Independently optimized ff value, with no assumed maximizer. -/
noncomputable def valueFF (M : Model) (c γ v : ℝ) : EReal :=
  ⨆ (s : ℝ≥0) (q : ℝ≥0), (profitFF M c γ v s q : EReal)

/- The definitions also accept parameters outside the economic hypotheses, but assert no
unboundedness result for them. For example, negative c alone does not force an infinite
value: at ρ=1 no primary order is paid for. All theorem uses impose their economic bounds. -/

/-- Admissible reservation fee at fixed primary and exercise costs (§3, pp. 10–11). -/
def AdmissibleFee (c v γ : ℝ) : Prop := 0 ≤ γ ∧ c < γ + v

end WangWebsterFlexibility.Threshold


