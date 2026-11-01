-- Prove2me | Definitions.Def_MaxWeightInstab_IsMaxWeight
-- name    : MaxWeightInstab_IsMaxWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:14:30.586986+00:00
-- url     : https://prove2.me/theorems/854baa79-d173-4b8e-a19a-f7a380664399
-- title:
--   MaxWeight schedules: maximizers of (1)
-- statement:
--   Given queue lengths $Q$, a schedule $\sigma$ is a **MaxWeight schedule** if $\sigma\in\mathcal S$ and it solves
--
--   $$
--   \text{maximize}\ \sum_{j\in\mathcal J}Q_j\sigma_j\quad\text{over }\sigma\in\mathcal S .
--   $$
--
--   The maximum is over all of $\mathcal S$: a schedule may allocate more service to a queue than it holds, and the surplus is wasted.
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, display (1), p.1; (3), p.3

import Mathlib
import Definitions.Def_MaxWeightInstab_IsSchedule

namespace MaxWeightInstab

/-- `σ` is a MaxWeight schedule for the queue lengths `x`: it solves (1),
"maximize `∑_{j∈𝒥} Q_j σ_j` over `σ ∈ 𝒮`" (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, display (1), p.1), with `𝒮` given by (3).

**Formalization Note.** The maximum is over all of `𝒮`, not over schedules capped by the queue
lengths: a schedule may assign more service to a queue than it holds (the surplus is wasted,
departures are `min(σ_j, Q_j)`, (8) p.5). -/
def IsMaxWeight {J : ℕ} (ν : ℕ) (x σ : State J) : Prop :=
  IsSchedule ν σ ∧ ∀ σ' : State J, IsSchedule ν σ' → ∑ q, x q * σ' q ≤ ∑ q, x q * σ q

end MaxWeightInstab


