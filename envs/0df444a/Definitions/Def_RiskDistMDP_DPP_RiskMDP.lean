-- Prove2me | Definitions.Def_RiskDistMDP_DPP_RiskMDP
-- name    : RiskDistMDP_DPP_RiskMDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:17.95921+00:00
-- url     : https://prove2.me/theorems/576dd4ac-e773-48de-800d-b58e0488a5b0
-- title:
--   Risk-averse model: model data, discount $\gamma$, risk measures $\sigma_0,\sigma_{t,x}$
-- statement:
--   A **risk-averse model** consists of the model data $(\mu,P,\mathcal A,C)$, a discount factor $\gamma$ and the risk measures $\sigma_0$ and $(\sigma_{t,x})_{(t,x)\in\mathbb N\times\mathbb X}$ on $\mathcal P_b(\mathbb R)$.
--
--   Its standing assumptions (`RiskMDP.Standing`) are those that hold throughout the paper: the model conditions of `BorelMDP.Standing`, $\gamma\in[0,1]$, Definition 2.3 for $\sigma_0$ and every $\sigma_{t,x}$, and Assumption 2.6. `RiskMDP.Normalized` says that $\sigma_{t,x}(\delta_0)=0$ for every $(t,x)\in\mathbb N\times\mathbb X$; it says nothing about $\sigma_0$.
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, §2.4, p. 8; p. 9; §2.5, p. 13

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_BorelMDP
import Definitions.Def_RiskDistMDP_DPP_Assumption26

set_option autoImplicit false

open MeasureTheory

namespace RiskDistMDP.DPP

/-- The risk-averse model of arXiv:2203.09612v4, §2.4–§2.5, pp.8–13: the model data of a
`BorelMDP` together with the discount factor `γ` (p.9) and the risk measures `σ₀` and
`(σ_{t,x})_{(t,x) ∈ ℕ × 𝕏}` (§2.4, p.8).

**Formalization Note** `σ t x` is `σ_{t,x}`, a function on `Measure ℝ` with values in `EReal`
(see `IsDistRiskMeasure`); only `t ≥ 1` is used. -/
structure RiskMDP (𝕏 𝔸 : Type*) [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] extends BorelMDP 𝕏 𝔸 where
  /-- the discount factor `γ` -/
  γ : ℝ
  /-- the risk measure `σ₀` at time `0` -/
  σ0 : Measure ℝ → EReal
  /-- the risk measures `σ_{t,x}` -/
  σ : ℕ → 𝕏 → Measure ℝ → EReal

/-- The standing assumptions of arXiv:2203.09612v4 on a `RiskMDP`: the model conditions
(`BorelMDP.Standing`), `γ ∈ [0, 1]` (p.9), `σ₀` and every `σ_{t,x}` satisfy Definition 2.3
(`IsRiskFamily`, §2.4, p.8), and Assumption 2.6 (p.8). -/
structure RiskMDP.Standing {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸]
    [TopologicalSpace 𝕏] [TopologicalSpace 𝔸] (R : RiskMDP 𝕏 𝔸) : Prop where
  model : R.toBorelMDP.Standing
  γ_nonneg : 0 ≤ R.γ
  γ_le_one : R.γ ≤ 1
  risk : IsRiskFamily R.σ0 R.σ
  assumption_2_6 : Assumption26 R.σ

/-- `(σ_{t,x})_{(t,x) ∈ ℕ × 𝕏}` is normalized (arXiv:2203.09612v4, p.9). Nothing is said about
`σ₀`. -/
def RiskMDP.Normalized {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸]
    (R : RiskMDP 𝕏 𝔸) : Prop :=
  FamilyNormalized R.σ

end RiskDistMDP.DPP


