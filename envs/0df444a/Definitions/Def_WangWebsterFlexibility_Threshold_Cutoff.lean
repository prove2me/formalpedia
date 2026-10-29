-- Prove2me | Definitions.Def_WangWebsterFlexibility_Threshold_Cutoff
-- name    : WangWebsterFlexibility_Threshold_Cutoff
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:33:32.569538+00:00
-- url     : https://prove2.me/theorems/4f3e07d7-540e-455e-8b45-50d5b8258a25
-- title:
--   Backup-cost threshold predicate
-- statement:
--   Fix a model, primary cost $c$, and exercise cost $v$. A finite real $\Gamma$ is a threshold if all four conditions hold:
--
--   1. Some admissible fee $\gamma$ has $\gamma+v\le\Gamma$.
--   2. Every admissible fee with $\gamma+v\le\Gamma$ satisfies $U_{df}(c,\gamma,v)\ge U_{ff}(c,\gamma,v)$.
--   3. Every admissible fee with $\gamma+v>\Gamma$ satisfies $U_{ff}(c,\gamma,v)\ge U_{df}(c,\gamma,v)$.
--   4. Some admissible fee with $\gamma+v>\Gamma$ satisfies $U_{ff}(c,\gamma,v)>U_{df}(c,\gamma,v)$.
--
--   Here admissibility means $\gamma\ge0$ and $\gamma+v>c$. The exercise cost remains fixed while the reservation fee varies. This predicate expresses the strong single-crossing reading of the source's ambiguous “some” on p. 21 using “for any” and the reverse inequality on A16. It asserts neither that a threshold exists nor that it is unique or differentiable.
-- source:
--   Wang and Webster (2021), Product Flexibility Strategy Under Supply and Demand Risk, Manufacturing & Service Operations Management, https://doi.org/10.1287/msom.2021.1037, Proposition 8(a), printed/PDF p. 21; Appendix A2, printed A16 / PDF 53

import Definitions.Def_WangWebsterFlexibility_Threshold_Profits

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


import Definitions.Def_WangWebsterFlexibility_Threshold_Model
import Mathlib.Data.EReal.Basic

open scoped NNReal

namespace WangWebsterFlexibility.Threshold

/-- Equation (4): independent primary failures, reservation paid up front, primary paid
on delivery including unsold units. Decisions are all nonnegative finite real numbers. -/
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

/-- Admissible reservation fee at fixed primary and exercise costs (§3, pp. 10–11). -/
def AdmissibleFee (c v γ : ℝ) : Prop := 0 ≤ γ ∧ c < γ + v

end WangWebsterFlexibility.Threshold

-/

namespace WangWebsterFlexibility.Threshold

/-- The strong single-crossing reading of Proposition 8(a) (p. 21 and A16).
Existence, uniqueness and regularity are deliberately not fields of the model. -/
def IsThreshold (M : Model) (c v Γ : ℝ) : Prop :=
  (∃ γ : ℝ, AdmissibleFee c v γ ∧ γ + v ≤ Γ) ∧
  (∀ γ : ℝ, AdmissibleFee c v γ → γ + v ≤ Γ →
    valueFF M c γ v ≤ valueDF M c γ v) ∧
  (∀ γ : ℝ, AdmissibleFee c v γ → Γ < γ + v →
    valueDF M c γ v ≤ valueFF M c γ v) ∧
  (∃ γ : ℝ, AdmissibleFee c v γ ∧ Γ < γ + v ∧
    valueDF M c γ v < valueFF M c γ v)

end WangWebsterFlexibility.Threshold


