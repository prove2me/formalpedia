-- Prove2me | Definitions.Def_PushInfoShare_profit
-- name    : PushInfoShare_profit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:07.761194+00:00
-- url     : https://prove2.me/theorems/30e2f0d5-5fde-4751-ac78-1ea4a0643cba
-- title:
--   Equilibrium expected profit $\Pi_i$
-- statement:
--   Manufacturer $i$'s expected profit along a profile is
--   $$\Pi_i=E[w_iq_i],\qquad w_i=\alpha_i+B_iY_i.$$
--   The profit is computed from the strategies and retains both the part proportional to $a^2$ and the part proportional to $\sigma$.
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), eq. (3), p.10

import Mathlib
import Definitions.Def_PushInfoShare_payoff

open MeasureTheory

namespace PushInfoShare

/-- Manufacturer `i`'s expected profit `Πᵢ = E[wᵢ qᵢ]` along the profile `str`, Jain, SSRN:3388957
(PDF of 2021-04-25), eq. (3), p.10: `payoff` at the linear rule `y ↦ α i + B i * y`. -/
noncomputable def profit {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Fin 2 → Ω → ℝ)
    (str : Profile) (i : Fin 2) : ℝ :=
  payoff μ Y str i fun y => str.α i + str.B i * y

end PushInfoShare


