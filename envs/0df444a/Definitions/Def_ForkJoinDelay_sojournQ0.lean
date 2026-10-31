-- Prove2me | Definitions.Def_ForkJoinDelay_sojournQ0
-- name    : ForkJoinDelay_sojournQ0
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:28:30.301255+00:00
-- url     : https://prove2.me/theorems/9d61725d-69ee-4fbb-b6c9-fcb9d75d4692
-- title:
--   Departure epochs from the first station; the sojourn time $S_0$
-- statement:
--   A tagged customer arrives at time $0$ at the single-server FCFS station $Q_0$ and finds $k$ customers there (in queue and in service). With service times $V_0,V_1,\dots$, where $V_0$ is the remaining service of the customer in service (or the tagged customer's own service if $k=0$), the $j$-th departure from $Q_0$ happens at
--
--   $$A_j=V_0+V_1+\cdots+V_j,\qquad j=0,\dots,k,$$
--
--   and the tagged customer is departure $j=k$. Its sojourn time in $Q_0$ is $S_0=A_k$.
--
--   **Formalization Note** No customers arriving after the tagged customer are modelled; under FCFS they do not influence $S_0$ or $S_{FJ}$ (p.8).
-- source:
--   Carmeli, Yom-Tov, Boxma, State-Dependent Estimation of Delay Distributions in Fork-Join Networks, author manuscript (sha256 c8b2002d…9d1c), §2, p.8 (definition of k and S0)

import Mathlib

namespace ForkJoinDelay

/-- **Departure epochs from the first station, and the tagged customer's sojourn time `S₀`.**
Carmeli, Yom-Tov, Boxma, *State-Dependent Estimation of Delay Distributions in Fork-Join
Networks*, author manuscript, §2, p.8: "k is the number of customers in the first single-server
station (including customers in queue and in service)"; "Let S0 be the tagged customer's sojourn
time in the first station".

The tagged customer arrives at time `0` and finds `k` customers at the single-server FCFS
station `Q₀`. With service times `V 0, V 1, …` (`V 0` the remaining service of the customer in
service, or the tagged customer's own service if `k = 0`), the `j`-th departure from `Q₀`
(`j = 0, …, k`) happens at
`A_j = V 0 + ⋯ + V j`, and the tagged customer is departure `j = k`.
`sojournQ0 V j ω` is `A_j`; in particular `S₀ = sojournQ0 V k ω`.

**Formalization Note.** Customers arriving after the tagged customer are not modelled (p.8:
"It can therefore be assumed that no customers enter the system after the tagged customer"). -/
def sojournQ0 {Ω : Type*} (V : ℕ → Ω → ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), V i ω

end ForkJoinDelay


