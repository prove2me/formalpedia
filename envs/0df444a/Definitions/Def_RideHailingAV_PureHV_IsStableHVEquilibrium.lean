-- Prove2me | Definitions.Def_RideHailingAV_PureHV_IsStableHVEquilibrium
-- name    : RideHailingAV_PureHV_IsStableHVEquilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:21:07.374989+00:00
-- url     : https://prove2.me/theorems/458439ca-aea0-4c8f-81ed-dde818805d9f
-- title:
--   Stable pure-HV equilibrium (Definition 1)
-- statement:
--   An equilibrium with demand rate $d$ (in the scenario of mass $m_i$) is **stable** if there is no $\epsilon>0$ such that
--   $$r_i(d-\epsilon)<w(\underline n(d-\epsilon))\,\underline n(d-\epsilon)\quad\text{and}\quad r_i(d+\epsilon)>w(\underline n(d+\epsilon))\,\underline n(d+\epsilon).$$
--   Equivalently, the revenue curve does not cross the cost curve from below at $d$: a small perturbation of the number of drivers is pushed back rather than amplified.
--
--   **Formalization Note** The perturbations $\epsilon$ range over those keeping $d-\epsilon$ and $d+\epsilon$ in the demand domain $[0,m_i]$. This changes no maximal stable equilibrium: beyond $m_i$ the revenue is negative and the cost positive.
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), Definition 1, p. 13

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market
import Definitions.Def_RideHailingAV_PureHV_IsHVEquilibrium

namespace RideHailingAV.PureHV

/-- **Stable pure-HV equilibrium.** Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023), Definition 1, p. 13: "An equilibrium with demand
rate `d_HV` is stable if there is no `ε > 0` such that `r_i(d_HV − ε) < w(n(d_HV − ε)) n(d_HV − ε)`
and `r_i(d_HV + ε) > w(n(d_HV + ε)) n(d_HV + ε)`."

**Formalization Note.** The perturbations `ε` are those keeping both `d − ε` and `d + ε` in the
demand domain `[0, m]` of (3). For the paper's revenue and cost this changes no maximal stable
equilibrium: beyond `m` the revenue is negative and the cost positive, so the excluded `ε` could
not witness instability of the largest equilibrium either. -/
def IsStableHVEquilibrium (M : Market) (m d : ℝ) : Prop :=
  IsHVEquilibrium M m d ∧
    ¬ ∃ ε : ℝ, 0 < ε ∧ 0 ≤ d - ε ∧ d + ε ≤ m ∧
      revenue M m (d - ε) < laborCost M (d - ε) ∧ laborCost M (d + ε) < revenue M m (d + ε)

end RideHailingAV.PureHV


