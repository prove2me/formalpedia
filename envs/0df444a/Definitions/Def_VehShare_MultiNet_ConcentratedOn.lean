-- Prove2me | Definitions.Def_VehShare_MultiNet_ConcentratedOn
-- name    : VehShare_MultiNet_ConcentratedOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:47:07.388845+00:00
-- url     : https://prove2.me/theorems/dbb1ce46-9639-487b-a7a0-d8b6d4487b5d
-- title:
--   A distribution concentrated on an allocation class
-- statement:
--   A distribution $\pi$ on the states is **concentrated on the allocation** $(K_c)$ if every state $x$ with $\pi(x)\neq0$ has allocation $(K_c)$. This is the steady state of the static chain "with the vehicles allocated" by $K_c$ to network $c$ (§6, p. 17).
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, §6, p. 17

import Mathlib
import Definitions.Def_VehShare_MultiNet_OnAllocation

namespace VehShare.MultiNet

/-- **A distribution concentrated on an allocation class.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), §6, p. 17 (the system "with the vehicles allocated" by `K_c` to network `c`).

Every state charged by `π` has allocation `Kc`. -/
def ConcentratedOn (P : Instance) {K : ℕ} (qs : P.L → P.L → ℝ)
    (Kc : (flowGraph P qs).ConnectedComponent → ℕ) (π : State P K → ℝ) : Prop :=
  ∀ z, π z ≠ 0 → OnAllocation P qs Kc z

end VehShare.MultiNet


