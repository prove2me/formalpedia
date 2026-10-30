-- Prove2me | Definitions.Def_VehShare_MultiNet_vehiclesIn
-- name    : VehShare_MultiNet_vehiclesIn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:45:47.572853+00:00
-- url     : https://prove2.me/theorems/d7f51037-21c5-4d07-b360-b9552e4e01c9
-- title:
--   Number of vehicles in a network
-- statement:
--   For a network $c$ of $q^s$ and a state $x$, the **number of vehicles in $c$** is the number at the locations of $c$ plus the number in the stages of the transit queues of the live pairs $(i,j)$ with $i\in\mathcal N_c$. It is the allocation $K_c$ of Problem (8) (p. 17).
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, §6, p. 17

import Mathlib
import Definitions.Def_VehShare_MultiNet_State
import Definitions.Def_VehShare_MultiNet_flowGraph
import Definitions.Def_VehShare_MultiNet_live

namespace VehShare.MultiNet

open Classical in
/-- **Number of vehicles in network `c` in state `z`.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), §6, p. 17 (the allocation `K_c` of vehicles to network `c`).

The vehicles at the locations of `c` plus those in the stages of the transit queues of the live pairs
`(i, j)` with `i` in `c`. -/
noncomputable def vehiclesIn (P : Instance) {K : ℕ} (qs : P.L → P.L → ℝ)
    (c : (flowGraph P qs).ConnectedComponent) (z : State P K) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i => (flowGraph P qs).connectedComponentMk i = c),
    (z.1 (Sum.inl i) +
      ∑ j ∈ Finset.univ.filter (fun j => live P qs i j), ∑ s, z.1 (Sum.inr ⟨(i, j), s⟩))

end VehShare.MultiNet


