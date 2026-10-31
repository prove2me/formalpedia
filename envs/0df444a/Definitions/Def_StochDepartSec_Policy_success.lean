-- Prove2me | Definitions.Def_StochDepartSec_Policy_success
-- name    : StochDepartSec_Policy_success
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:38.145993+00:00
-- url     : https://prove2.me/theorems/059f20c0-0216-43e9-9b01-e606e258708d
-- title:
--   The success event $\mathrm{success}(\mathrm{pol})$
-- statement:
--   A policy **succeeds** in outcome $\omega$ if it accepts the best candidate overall (rank $0$) and accepts no candidate at a strictly earlier time. Because acceptance is irrevocable, the first acceptance is the policy's selection; because at most one candidate is accepted per instant, the first acceptance is unique.
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, §2, p.5; §3, p.7

import Mathlib
import Definitions.Def_StochDepartSec_Outcome
import Definitions.Def_StochDepartSec_dep
import Definitions.Def_StochDepartSec_Policy

namespace StochDepartSec

/-- `success(pol)`: the policy's first acceptance is the best candidate overall, i.e. the best
candidate (overall rank 0) is accepted and no candidate is accepted at a strictly earlier time.
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, §3, p.7: "Given any policy pol, we denote by success(pol) the event that pol selects the best
candidate"; §2, p.5: "The algorithm is successful if it chooses i ∈ [n] such that π(i) = 1."

**Formalization Note** Acceptance is irrevocable, so only the first acceptance is the selection;
at most one candidate is accepted per instant (decisions are `Option (Fin n)`), so the first
acceptance is unique. Rank 0 is the paper's `π(i) = 1`. -/
def Policy.success {n : ℕ} (pol : Policy n) (ω : Outcome n) : Prop :=
  ∃ i, (rank ω i : ℕ) = 0 ∧ pol.Accepts ω i ∧ ∀ j, pol.Accepts ω j → dep ω i ≤ dep ω j

end StochDepartSec


