-- Prove2me | Definitions.Def_WangWebsterFlexibility_Threshold_Benefits
-- name    : WangWebsterFlexibility_Threshold_Benefits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:33:02.054289+00:00
-- url     : https://prove2.me/theorems/cfc5ad54-718a-4bec-bdfc-9af3c10ea615
-- title:
--   Demand pooling and supplier diversification benefits
-- statement:
--   At any $s,q_1,q_2\ge0$, define the demand pooling benefit
--   $$DP(s,q_1,q_2)=(1-\rho)E[R_{ff}(D;q_1+q_2,s)-R(D;q_1,q_2,s)].$$
--   Put $A=(s-(D_1-q_1)^+)^+$ and $B=(s-D_1)^+$. Define the supplier diversification benefit by
--   $$SD(s,q_1,q_2)=(\pi_2-v)\rho(1-\rho)E[\min(A,D_2)-\min(A,(D_2-q_2)^+)+\min(B,(D_2-q_2)^+)-\min(B,D_2)].$$
--   These are concrete bounded-sales expectations, independent of the primary and reservation costs. They do not assume a profit decomposition, nonnegativity, or any dominance conclusion.
--
--   Product 1 is deterministic if its demand equals some nonnegative real constant almost surely. A finite $s\ge0$ is the essential upper endpoint of total demand if $D_1+D_2\le s$ almost surely and $P(D_1+D_2>t)>0$ for every real $t<s$. The endpoint predicate can fail for every finite $s$; no bounded-support assumption is imposed.
-- source:
--   Wang and Webster (2021), Product Flexibility Strategy Under Supply and Demand Risk, Manufacturing & Service Operations Management, https://doi.org/10.1287/msom.2021.1037, §4.2, printed/PDF p. 18; Appendix A2, printed A7–A9 / PDF 44–46

import Definitions.Def_WangWebsterFlexibility_Threshold_Model

open MeasureTheory

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

/-- Demand pooling benefit at the same total primary order (§4.2, p. 18; A7). -/
noncomputable def DP (M : Model) (v : ℝ) (s q₁ q₂ : ℝ≥0) : ℝ :=
  (1 - M.ρ) * M.expect (fun d =>
    revenueFF M v d ((q₁ : ℝ) + (q₂ : ℝ)) s - revenueDF M v d q₁ q₂ s)

/-- Supplier diversification benefit from the four backup allocations (p. 18; A7–A8).
Neither primary cost nor reservation fee occurs in this expression. -/
noncomputable def SD (M : Model) (v : ℝ) (s q₁ q₂ : ℝ≥0) : ℝ :=
  (M.π₂ - v) * M.ρ * (1 - M.ρ) * M.expect (fun d =>
    let A := pos ((s : ℝ) - pos ((d.1 : ℝ) - (q₁ : ℝ)))
    let B := pos ((s : ℝ) - (d.1 : ℝ))
    min A (d.2 : ℝ) - min A (pos ((d.2 : ℝ) - (q₂ : ℝ))) +
      min B (pos ((d.2 : ℝ) - (q₂ : ℝ))) - min B (d.2 : ℝ))

/-- Product 1 is almost surely constant, including the zero constant. -/
def DeterministicFirst (M : Model) : Prop :=
  ∃ a : ℝ≥0, ∀ᵐ d ∂(M.demand₁ : Measure ℝ≥0), d = a

/-- Finite essential upper endpoint of total demand, interpreting max{D₁+D₂} in
Proposition 6(b). This predicate is simply false for every finite s if support is unbounded. -/
def TotalDemandEndpoint (M : Model) (s : ℝ≥0) : Prop :=
  (∀ᵐ d ∂M.law, (d.1 : ℝ) + (d.2 : ℝ) ≤ (s : ℝ)) ∧
    ∀ t : ℝ, t < (s : ℝ) → 0 < M.law {d | t < (d.1 : ℝ) + (d.2 : ℝ)}

end WangWebsterFlexibility.Threshold


