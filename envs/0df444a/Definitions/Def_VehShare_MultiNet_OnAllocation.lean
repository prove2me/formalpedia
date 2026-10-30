-- Prove2me | Definitions.Def_VehShare_MultiNet_OnAllocation
-- name    : VehShare_MultiNet_OnAllocation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:46:37.790067+00:00
-- url     : https://prove2.me/theorems/25a9359f-ee6c-4919-aebd-738a7f45c322
-- title:
--   States with a given vehicle allocation
-- statement:
--   A state $x$ has **allocation** $(K_c)_c$ if every transit queue of a pair that is not live is empty and network $c$ holds exactly $K_c$ vehicles, for every $c$ (the allocation of Problem (8), $\sum_c K_c=K$, p. 17).
--
--   **Formalization Note** Transit queues without flow under $q^s$ are transient under the static policy, so the allocation class requires them to be empty.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, §6, p. 17, Problem (8)

import Mathlib
import Definitions.Def_VehShare_MultiNet_vehiclesIn

namespace VehShare.MultiNet

/-- **States with the vehicle allocation `(K_c)_c`.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), §6, p. 17, Problem (8) (an allocation `K_c`, `∑_c K_c = K`, of the vehicles to the networks).

`z` has no vehicle in the transit queue of a pair that is not live, and exactly `Kc c` vehicles in
network `c`, for every `c`.

**Formalization Note.** Reading 4: transit queues of pairs without flow under `q^s` are transient
under the static policy, so the allocation class requires them empty. -/
def OnAllocation (P : Instance) {K : ℕ} (qs : P.L → P.L → ℝ)
    (Kc : (flowGraph P qs).ConnectedComponent → ℕ) (z : State P K) : Prop :=
  (∀ i j (s : P.Ph i j), ¬ live P qs i j → z.1 (Sum.inr ⟨(i, j), s⟩) = 0) ∧
    ∀ c, vehiclesIn P qs c z = Kc c

end VehShare.MultiNet


