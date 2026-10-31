-- Prove2me | Definitions.Def_KashUpgrade_IsTerminalRun
-- name    : KashUpgrade_IsTerminalRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:21:52.137956+00:00
-- url     : https://prove2.me/theorems/c71f1fbd-0d6c-427d-a8d3-2824f70ca4dd
-- title:
--   A terminating run of OptimalLumping
-- statement:
--   A state $(\mathcal L,\gamma)$ is the end of a terminating run of OptimalLumping if it is reached by finitely many iterations from $\mathcal L=\emptyset$ and $\gamma_i=c/(s_i-s_{i-1})$, and $S=\emptyset$ there. The algorithm returns this $\gamma$.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), Algorithm 1, p.19

import Mathlib
import Definitions.Def_KashUpgrade_OLStep
import Definitions.Def_KashUpgrade_initialGamma

namespace KashUpgrade

/-- **A terminating run of OptimalLumping.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), Algorithm 1, p.19: `st = (L, γ)` is reached from
`L = ∅` and `γ_i = c / (s_i - s_{i-1})` by iterations of the loop, and the loop stops there, i.e.
`S = ∅`. The algorithm returns the `γ` of this state. -/
def IsTerminalRun (c : ℝ) (s : ℕ → ℕ) (A : ℕ → ℝ) (j n : ℕ)
    (st : Finset ℕ × (ℕ → ℝ)) : Prop :=
  Relation.ReflTransGen (OLStep c s A j n) (∅, initialGamma c s) st ∧
    violators j n st.2 = ∅

end KashUpgrade


