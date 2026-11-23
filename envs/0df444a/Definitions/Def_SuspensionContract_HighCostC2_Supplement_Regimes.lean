-- Prove2me | Definitions.Def_SuspensionContract_HighCostC2_Supplement_Regimes
-- name    : SuspensionContract_HighCostC2_Supplement_Regimes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:01:54.483554+00:00
-- url     : https://prove2.me/theorems/09d00077-f080-4f5a-a730-3c19bcce56ae
-- title:
--   Published parameter transports, revenue thresholds and the canonical control-band contract
-- statement:
--   All eight parameter fields are copied, without changing values, into the already-published Condition 1, always-work and control-band records. No published definition is redeclared. The high-cost threshold is $\bar K_1$ under Condition 1 and $\bar K_2$ under Condition 2; revenue comparative statics vary $R$ alone on $R\Delta\mu>c$.
--
--   The control-band parameters are computed by the source construction:
--   $$\psi(\underline\vartheta)=K,\quad \hat{\mathbf w}=\tilde w(\underline\vartheta),\quad \mathsf c=C(\underline\vartheta),\quad \bar\vartheta=\bar\theta(\underline\vartheta).$$
--   The root is selected on $(0,\underline\theta^0)$ in Condition 1 and $(\breve\theta,\underline\theta^0)$ in Condition 2. Formula (47) then supplies the lower working boundary $\max(\underline\vartheta,\check w(\hat{\mathbf w}))$. All analytic functions are imported from published definitions. In particular the lower switching-cost threshold uses the published correction of (33), with $((\rho-\mu)/\rho)\beta$ rather than the printed $(r/\rho)\beta$.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript (2023-03-15), SHA-256 39e9a1afe4665462f93250c221173be577581eb346a2679660d4de54a49b3304, pp.22–28, (K1), (K2), (33), (46)–(47); ec34–ec40, (EC.70)–(EC.78)

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC2_Supplement_BandContracts
import Definitions.Def_SuspensionContract_HighCostC1_Thresholds
import Definitions.Def_SuspensionContract_AlwaysWork_Setting
import Definitions.Def_SuspensionContract_ControlBand_Construction
import Definitions.Def_SuspensionContract_ControlBand_Thresholds

namespace SuspensionContract.HighCostC2.Supplement

open Set

/-- Only a record transport: every field is copied into the already-published Condition 1 model. -/
def toC1 (P : Params) : SuspensionContract.HighCostC1.Params :=
  ⟨P.R, P.μ, P.μlow, P.b, P.c, P.K, P.r, P.ρ⟩

/-- Only a record transport into the already-published always-work model. -/
def toAW (P : Params) : SuspensionContract.AlwaysWork.Params :=
  ⟨P.R, P.μ, P.μlow, P.b, P.c, P.K, P.r, P.ρ⟩

/-- Only a record transport into the already-published control-band model. -/
def toCB (P : Params) : SuspensionContract.ControlBand.Params :=
  ⟨P.R, P.μ, P.μlow, P.b, P.c, P.K, P.r, P.ρ⟩

open Classical in
/-- The main-text threshold K̄: K̄₁ in Condition 1, K̄₂ in Condition 2 (p.24). -/
noncomputable def highThreshold (P : Params) : ℝ :=
  if P.Condition1 then (toC1 P).Kbar1 else P.Kbar2

/-- Vary revenue per arrival, fixing all other model primitives. -/
def withRevenue (P : Params) (R : ℝ) : Params := { P with R := R }

/-- Source Assumption 1's domain for comparative statics in R. -/
def RevenueDomain (P : Params) : Set ℝ := {R | P.c < R * (P.μ - P.μlow)}

open Classical in
/-- The EC.3.9 branch domain for the canonical quadruple. -/
noncomputable def rootDomain (P : Params) : Set ℝ :=
  if P.Condition1 then Ioo 0 (toCB P).theta0 else Ioo (toCB P).thetaBreve (toCB P).theta0C2

open Classical in
/-- Select the unique root of ψ(ϑ̲)=K from EC.3.9, not a quadruple assumed to satisfy the QVI. -/
noncomputable def lowerBandRoot (P : Params) : ℝ :=
  if h : ∃ θ ∈ rootDomain P, (toCB P).psi θ = P.K then Classical.choose h else 0

/-- Definition 1 parameters for the actual control-band contract (47). -/
noncomputable def optimalBand (P : Params) : Band :=
  let θ := lowerBandRoot P
  let wt := (toCB P).wtil θ
  ⟨θ, max θ ((toCB P).wcheck wt), (toCB P).thetaBar θ, wt⟩

/-- V_∅ of (46) for the canonical construction; the principal objective is V_∅(w)-w. -/
noncomputable def bandSuspensionValue (P : Params) : ℝ → ℝ :=
  let θ := lowerBandRoot P
  (toCB P).V046 ((toCB P).Cof θ) ((toCB P).wtil θ) ((toCB P).thetaBar θ)

end SuspensionContract.HighCostC2.Supplement


