-- Prove2me | Definitions.Def_RideHailingAV_PureHV_IsMaxStableHVEquilibrium
-- name    : RideHailingAV_PureHV_IsMaxStableHVEquilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:22:13.052576+00:00
-- url     : https://prove2.me/theorems/c5d1dcd9-b17e-4cfc-9a49-f7897862905b
-- title:
--   Maximal stable pure-HV equilibrium
-- statement:
--   A demand rate $d^*$ is a **maximal stable equilibrium** in the scenario of mass $m_i$ if it is a stable equilibrium (Definition 1) and every stable equilibrium $d$ satisfies $d\le d^*$. The paper restricts attention to it: "Henceforth, whenever we refer to an equilibrium it is a maximal stable equilibrium."
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), §4, p. 14 (unnumbered)

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market
import Definitions.Def_RideHailingAV_PureHV_IsStableHVEquilibrium

namespace RideHailingAV.PureHV

/-- **Maximal stable pure-HV equilibrium.** Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023), §4, p. 14 (unnumbered): "when there are
multiple stable equilibria, we focus on the one with the highest demand rate, called the maximal
stable equilibrium". `d` is a stable equilibrium (Definition 1) and every stable equilibrium
has demand at most `d`. -/
def IsMaxStableHVEquilibrium (M : Market) (m d : ℝ) : Prop :=
  IsStableHVEquilibrium M m d ∧ ∀ d', IsStableHVEquilibrium M m d' → d' ≤ d

end RideHailingAV.PureHV


