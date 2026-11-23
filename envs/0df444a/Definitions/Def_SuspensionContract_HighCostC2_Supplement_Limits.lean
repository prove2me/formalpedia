-- Prove2me | Definitions.Def_SuspensionContract_HighCostC2_Supplement_Limits
-- name    : SuspensionContract_HighCostC2_Supplement_Limits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:02:28.07572+00:00
-- url     : https://prove2.me/theorems/1ee7939b-e42b-4cfd-9ef1-b7defcd7e69b
-- title:
--   Positive-cost canonical branches and the full zero-cost limiting value
-- statement:
--   Fix every parameter except switching cost. The cost-free standing assumptions retain the arrival, effort, revenue and discount restrictions and omit $K>0$. The positive-cost domain consists of $K>0$ satisfying Condition 3. The limiting regime is Condition 1 with $\bar K_1>0$ or Condition 2 with $\underline K>0$.
--
--   The lower threshold is the source's unique root $\psi(\underline\vartheta(K))=K$ in the appropriate construction domain. The other quantities are $\bar\vartheta(K)=\bar\theta(\underline\vartheta(K))$, $\hat{\mathbf w}(K)=\tilde w(\underline\vartheta(K))$, and $\mathsf c(K)=C(\underline\vartheta(K))$. The common switching-threshold limit is the branch's turning point, as identified in the proof of Proposition 8. Given finite limits $w^0,c^0$, the limit value is
--   $$\mathbb V_{\theta_0}(w)=\begin{cases}V_{c^0}(w),&w\le\theta_0,\\ \mathcal V_{w^0}(w),&w>\theta_0.\end{cases}$$
--   Theorem 6, rather than the definition, asserts the limits and the zero-cost QVI. Selection defaults outside the proved construction domain carry no mathematical assertion.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript (2023-03-15), SHA-256 39e9a1afe4665462f93250c221173be577581eb346a2679660d4de54a49b3304, §5.1 p.29; EC.3.9 ec34–ec40; EC.4.1–EC.4.2 ec50–ec51

import Mathlib
import Definitions.Def_SuspensionContract_ControlBand_Construction
import Definitions.Def_SuspensionContract_ControlBand_Thresholds

namespace SuspensionContract.HighCostC2.Supplement

open MeasureTheory Filter Set
open scoped Topology

/-- The rate, cost and discount assumptions, with switching cost omitted so K=0 is allowed. -/
def CostFreeStanding (P : SuspensionContract.ControlBand.Params) : Prop :=
  (0 ≤ P.μlow ∧ P.μlow < P.μ) ∧ (0 < P.b ∧ P.b ≤ P.c) ∧
    (0 < P.r ∧ P.r ≤ P.ρ) ∧ P.c < P.R * (P.μ - P.μlow)

/-- Vary only the switching cost, keeping all seven other parameters fixed. -/
def withCost (P : SuspensionContract.ControlBand.Params) (K : ℝ) :
    SuspensionContract.ControlBand.Params := { P with K := K }

/-- Positive costs in Condition 3; both branches are retained. -/
def BandCosts (P : SuspensionContract.ControlBand.Params) : Set ℝ :=
  {K | 0 < K ∧ (withCost P K).Condition3}

/-- The nonempty limiting regime of EC.4.1–EC.4.2 (ec50–ec51). -/
def ZeroCostRegime (P : SuspensionContract.ControlBand.Params) : Prop :=
  (P.Condition1 ∧ 0 < P.Kbar1) ∨ (P.Condition2 ∧ 0 < P.Klow)

open Classical in
/-- The branch-specific domain in EC.3.9: (0,θ̲⁰) or (θ̲̆,θ̲⁰). -/
noncomputable def ConstructionDomain (P : SuspensionContract.ControlBand.Params) : Set ℝ :=
  if P.Condition1 then Set.Ioo 0 P.theta0 else Set.Ioo P.thetaBreve P.theta0C2

open Classical in
/-- The turning point, identified with θ₀ in the proof of Proposition 8 (ec50). -/
noncomputable def limitTheta (P : SuspensionContract.ControlBand.Params) : ℝ :=
  if P.Condition1 then P.theta0 else P.theta0C2

open Classical in
/-- Choose the root ψ(ϑ̲)=K from the source construction, not a quadruple selected by the QVI.
The root is unique on ConstructionDomain (EC.7/EC.11). If absent, the value is explicitly junk. -/
noncomputable def lowerTheta (P : SuspensionContract.ControlBand.Params) (K : ℝ) : ℝ :=
  if h : ∃ θ ∈ ConstructionDomain P, P.psi θ = K then Classical.choose h else 0

/-- ϑ̄(K)=θ̄(ϑ̲(K)), EC.3.9. -/
noncomputable def upperTheta (P : SuspensionContract.ControlBand.Params) (K : ℝ) : ℝ :=
  P.thetaBar (lowerTheta P K)

/-- 𝐰̂(K)=w̃(ϑ̲(K)), EC.3.9. -/
noncomputable def workingCutoff (P : SuspensionContract.ControlBand.Params) (K : ℝ) : ℝ :=
  P.wtil (lowerTheta P K)

/-- 𝖼(K)=C(ϑ̲(K)), EC.3.9. -/
noncomputable def bandCoefficient (P : SuspensionContract.ControlBand.Params) (K : ℝ) : ℝ :=
  P.Cof (lowerTheta P K)

/-- The full piecewise limit value of Theorem 6, including its branch at θ₀. -/
noncomputable def zeroValue (P : SuspensionContract.ControlBand.Params)
    (w0 c0 w : ℝ) : ℝ :=
  if w ≤ limitTheta P then P.Vc c0 w else P.calV w0 w

end SuspensionContract.HighCostC2.Supplement


