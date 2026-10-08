-- Prove2me | Definitions.Def_ReedGGN_SystemEq_NonIdling
-- name    : ReedGGN_SystemEq_NonIdling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:53.941296+00:00
-- url     : https://prove2.me/theorems/a9ccc356-faaa-4172-91fc-2803f394cf75
-- title:
--   Proof of Proposition 2.1, p. 8 — the non-idling FCFS identity (Q(t) − N)⁺ = Σ 1{t < w̃ᵢ} + Σ 1{τᵢ ≤ t < τᵢ + wᵢ}
-- statement:
--   A sample path of the $G/GI/N$ queue is **non-idling** if, for every $t\ge 0$, the number of customers waiting to be served is
--   $$(Q(t)-N)^+=\sum_{i=1}^{(Q_0-N)^+}1\{t<\tilde w_i\}+\sum_{i=1}^{A(t)}1\{\tau_i\le t<\tau_i+w_i\}.$$
--   The first sum counts the initial customers $N+i$ that have not yet entered service at time $t$, and the second counts the arrivals that have arrived by time $t$ and are still waiting.
--
--   This is the identity with which the proof of Proposition 2.1 opens (p. 8). It expresses that the system serves first come first served and never leaves a server idle while a customer waits; Section 5 refers to this as "the system is operating under a nonidling policy" (p. 28). It is the only modelling hypothesis of Proposition 2.1 and of the system equation (2.8).
--
--   **Formalization Note** The paper does not construct the waiting times $w_i$, $\tilde w_i$ from the arrival and service times; it takes them as given and uses this identity. The formalization does the same: non-idling is a property of a sample path, satisfied by every sample path of an $N$-server first-come-first-served system that does not idle while customers wait.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 8, proof of Proposition 2.1 (first display); p. 28 (nonidling policy)

import Mathlib
import Definitions.Def_ReedGGN_SystemEq_QueueLength

namespace ReedGGN.SystemEq

/-- The non-idling (FCFS) property of a sample path, as stated at the start of the proof of
Proposition 2.1 (p. 8): for every `t ≥ 0`, the number of customers waiting to be served,
`(Q(t) − N)⁺`, equals the number of initial customers `N + i` still waiting at time `t`
(`t < w̃_i`) plus the number of arrivals that have arrived but not yet entered service
(`τ_i ≤ t < τ_i + w_i`):
`(Q(t) − N)⁺ = Σ_{i=1}^{(Q₀−N)⁺} 1{t < w̃_i} + Σ_{i=1}^{A(t)} 1{τ_i ≤ t < τ_i + w_i}`.
Every sample path of an `N`-server first-come-first-served system that never idles a server
while a customer waits satisfies it; the paper takes it as given. -/
def NonIdling (P : SamplePath) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    max ((Q P t : ℝ) - P.N) 0 =
      (∑ i ∈ Finset.Icc 1 (P.Q₀ - P.N), if t < P.wt i then (1 : ℝ) else 0) +
      ∑ i ∈ Finset.Icc 1 (P.A t), if P.τ i ≤ t ∧ t < P.τ i + P.w i then (1 : ℝ) else 0

end ReedGGN.SystemEq


