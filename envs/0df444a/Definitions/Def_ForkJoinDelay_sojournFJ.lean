-- Prove2me | Definitions.Def_ForkJoinDelay_sojournFJ
-- name    : ForkJoinDelay_sojournFJ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:18.13498+00:00
-- url     : https://prove2.me/theorems/2fa9fd72-050c-4f7f-9018-dc2e820245a8
-- title:
--   The fork-join sojourn time $S_{FJ}=\max\{S_1,S_2\}$
-- statement:
--   In the state $(k,h_1,h_2)$ at the tagged customer's arrival, the upper station UFJ holds $h_1$ customers and the lower station LFJ holds $h_2$ (in queue and in service). Both are single-server FCFS stations fed by the departures $A_0,\dots,A_k$ of $Q_0$: every customer leaving $Q_0$ joins both.
--
--   At UFJ the $h_1$ customers present have service times $U_0,\dots,U_{h_1-1}$ (with $U_0$ the remaining service of the customer in service), so this backlog clears at $D_{-1}=U_0+\cdots+U_{h_1-1}$ ($0$ if $h_1=0$). The $j$-th customer from $Q_0$ needs $U_{h_1+j}$ and leaves at
--
--   $$D_j=\max(D_{j-1},A_j)+U_{h_1+j}.$$
--
--   LFJ is the same with $G$, $h_2$ and departure epochs $D'_j$. The tagged customer ($j=k$) has sojourn times $S_1=D_k-A_k$ at UFJ and $S_2=D'_k-A_k$ at LFJ, and leaves the network when both are done:
--
--   $$S_{FJ}=\max\{S_1,S_2\}.$$
-- source:
--   Carmeli, Yom-Tov, Boxma, State-Dependent Estimation of Delay Distributions in Fork-Join Networks, author manuscript (sha256 c8b2002d…9d1c), §2, p.8 (definitions of h1, h2, S1, S2, SFJ = max{S1,S2}; customers join both stations); Figure 2, p.9

import Mathlib
import Definitions.Def_ForkJoinDelay_fcfsDeparture
import Definitions.Def_ForkJoinDelay_sojournQ0

namespace ForkJoinDelay

/-- **The tagged customer's sojourn time `S_FJ = max {S₁, S₂}` in the fork-join part.**
Carmeli, Yom-Tov, Boxma, *State-Dependent Estimation of Delay Distributions in Fork-Join
Networks*, author manuscript, §2, p.8: "All customers first receive service in Q0 and then
simultaneously join UFJ and LFJ"; "h1 is the number of customers in the UFJ station, and h2 is
the number of customers in the LFJ station"; "SFJ = max{S1,S2}".

At the tagged customer's arrival (time `0`) the upper station UFJ holds `h₁` customers and the
lower station LFJ holds `h₂` (queue and service). Both are single-server FCFS stations fed by the
departures `A_0, …, A_k` of `Q₀` (`sojournQ0`). At UFJ the `h₁` customers present have service
times `U 0, …, U (h₁ - 1)`, so the backlog clears at `U 0 + ⋯ + U (h₁ - 1)`, and the `j`-th
customer from `Q₀` needs `U (h₁ + j)`; its departure epoch is `D_j` of `fcfsDeparture`. LFJ is
the same with `G` and `h₂`. The tagged customer (`j = k`) has sojourn times
`S₁ = D_k - A_k` at UFJ and `S₂ = D'_k - A_k` at LFJ, and
`S_FJ = max S₁ S₂`.

**Formalization Note.** `U 0` (resp. `G 0`) is the remaining service of the customer in service
at UFJ (LFJ), exponential by memorylessness (p.10). An empty station (`h = 0`) has backlog `0`
(empty sum). Customers arriving after the tagged customer are not modelled (p.8). -/
noncomputable def sojournFJ {Ω : Type*} (V U G : ℕ → Ω → ℝ) (k h₁ h₂ : ℕ) (ω : Ω) : ℝ :=
  max
    (fcfsDeparture (∑ i ∈ Finset.range h₁, U i ω) (fun j => sojournQ0 V j ω)
      (fun j => U (h₁ + j) ω) k - sojournQ0 V k ω)
    (fcfsDeparture (∑ i ∈ Finset.range h₂, G i ω) (fun j => sojournQ0 V j ω)
      (fun j => G (h₂ + j) ω) k - sojournQ0 V k ω)

end ForkJoinDelay


