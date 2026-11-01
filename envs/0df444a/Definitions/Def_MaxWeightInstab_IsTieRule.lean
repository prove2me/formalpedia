-- Prove2me | Definitions.Def_MaxWeightInstab_IsTieRule
-- name    : MaxWeightInstab_IsTieRule
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:15:29.226012+00:00
-- url     : https://prove2.me/theorems/557ae77c-31ec-450b-9693-11837e077d96
-- title:
--   MaxWeight policy with an arbitrary or random tie rule
-- statement:
--   A **MaxWeight policy** assigns to every queue-length vector $Q$ a schedule $\pi(Q)$ solving (1). "In the case of ties in (1), $\sigma$ may be chosen arbitrarily (or randomly) among these schedules." A tie rule is a map $\pi$ from queue-length vectors to probability distributions on schedules, each supported on the maximizers of (1) for that $Q$.
--
--   **Formalization Note** Deterministic tie rules are the point-mass case. The rule depends on the current queue lengths only, so the queue process is a time-homogeneous Markov chain.
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, p.1

import Mathlib
import Definitions.Def_MaxWeightInstab_IsMaxWeight

namespace MaxWeightInstab

/-- A MaxWeight policy with a tie rule: "In the case of ties in (1), σ may be chosen arbitrarily
(or randomly) among these schedules. We denote by π(Q) the schedule of the MaxWeight policy"
(Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, p.1). A rule `π` assigns to every vector of queue lengths a probability distribution on
schedules, supported on the maximizers of (1).

**Formalization Note.** Deterministic tie rules are the Dirac case `π x = PMF.pure (f x)`. The rule
depends on the current queue lengths only, so the queue process is a time-homogeneous Markov chain,
as the paper states (p.1, p.5). -/
def IsTieRule {J : ℕ} (ν : ℕ) (π : State J → PMF (State J)) : Prop :=
  ∀ x σ, σ ∈ (π x).support → IsMaxWeight ν x σ

end MaxWeightInstab


