-- Prove2me | Definitions.Def_RideHailingAV_PureHV_IsLooseMarket
-- name    : RideHailingAV_PureHV_IsLooseMarket
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:23:10.217435+00:00
-- url     : https://prove2.me/theorems/d1e2131f-32ca-409a-880f-11df5ee23c66
-- title:
--   Loose labor market (Assumption 2, eq. (18))
-- statement:
--   **Assumption 2 (loose market)** for the scenario of mass $m_i$: the revenue-maximizing price is at or above the human drivers' equilibrium price,
--   $$\arg\max_p\, r_i(d_i(p))\ \ge\ p^*_{HV,i}.\qquad(18)$$
--   Precisely: if $d^*$ is a maximal stable equilibrium of the scenario and $p^*=p_i(d^*)$ is its price, then every price $q\ge0$ that maximizes $p\mapsto r_i(d_i(p))$ over prices $p\ge0$ satisfies $q\ge p^*$. With uniform values the maximizer is $q=V/2$, so the assumption says $p^*\le V/2$.
--
--   **Formalization Note** This is the form (18) of the assumption. It is not replaced by condition (33) of Appendix B.1.1, $r_i(m_i/2)>w(\underline n(m_i/2))\underline n(m_i/2)$, which is strictly stronger: the two differ when $d^*=m_i/2$.
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), Assumption 2, eq. (18), p. 15

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market
import Definitions.Def_RideHailingAV_PureHV_demandAtPrice
import Definitions.Def_RideHailingAV_PureHV_IsMaxStableHVEquilibrium

namespace RideHailingAV.PureHV

/-- **Assumption 2 (loose market) for one scenario.** Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023), Assumption 2, eq. (18), p. 15:
"the revenue-maximizing price is at or above the human driver's equilibrium price, i.e.
`arg max_p r_i(d_i(p)) ≥ p*_HV,i`".

`IsLooseMarket M m` says: for the maximal stable equilibrium demand `d*` of the scenario of mass
`m`, every nonnegative price `q` maximizing the revenue `p ↦ r_i(d_i(p))` over prices `p ≥ 0`
satisfies `q ≥ p* = p_i(d*)` (eq. (47), p. 45).

**Formalization Note.** This is the form (18) of the assumption, not the condition (33) of
Appendix B.1.1, p. 42, which is strictly stronger (they differ when `d* = m/2`). -/
def IsLooseMarket (M : Market) (m : ℝ) : Prop :=
  ∀ d, IsMaxStableHVEquilibrium M m d →
    ∀ q, 0 ≤ q → IsMaxOn (fun p => revenue M m (demandAtPrice M m p)) (Set.Ici 0) q →
      invDemand M m d ≤ q

end RideHailingAV.PureHV


