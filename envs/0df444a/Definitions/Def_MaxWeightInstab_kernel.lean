-- Prove2me | Definitions.Def_MaxWeightInstab_kernel
-- name    : MaxWeightInstab_kernel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:15:16.505992+00:00
-- url     : https://prove2.me/theorems/9980362c-6258-49f0-8e88-9595bcc868f5
-- title:
--   One-step transition law of the MaxWeight queueing process
-- statement:
--   Under a MaxWeight tie rule $\pi$, the queueing network process $\mathcal Q$ moves from $Q$ by drawing a schedule $\sigma\sim\pi(Q)$, drawing the arrival pattern $e$ from the arrival law independently, and applying one time unit of the network. This is the transition law of the discrete-time countable-state Markov chain of the paper.
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, p.1, p.3, p.5

import Mathlib
import Definitions.Def_MaxWeightInstab_step
import Definitions.Def_MaxWeightInstab_arrivalLaw

namespace MaxWeightInstab

/-- The one-step transition law of the queueing network process `𝐐` of the network of Figure 1
under a MaxWeight policy with tie rule `π` (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, p.1, p.3, p.5): from queue lengths `x`, draw a
schedule `σ ∼ π(x)`, draw the external arrivals `e ∼ arrivalLaw a J` independently, and move to
`step x σ e`. -/
noncomputable def kernel {J : ℕ} (a : ℝ) (π : State J → PMF (State J)) (x : State J) :
    PMF (State J) :=
  (π x).bind fun σ => (arrivalLaw a J).map (step x σ)

end MaxWeightInstab


