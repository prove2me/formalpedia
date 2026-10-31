-- Prove2me | Definitions.Def_ForkJoinDelay_fcfsDeparture
-- name    : ForkJoinDelay_fcfsDeparture
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:28:29.408044+00:00
-- url     : https://prove2.me/theorems/148020c1-e948-46cd-a501-06aba929da8b
-- title:
--   Departure epochs of a single-server FCFS station
-- statement:
--   A single server first clears a backlog of work that ends at time $D_{-1}$ and then serves arriving customers $j=0,1,2,\dots$ in order of their arrival epochs $A_0\le A_1\le\cdots$, customer $j$ needing service time $s_j$. Under first-come-first-served, customer $j$ starts service when both the previous customer has left and it has arrived, so its departure epoch is
--
--   $$D_j=\max(D_{j-1},A_j)+s_j,\qquad j=0,1,2,\dots$$
--
--   This is the departure-time recursion of a single-server FCFS queue. It is used for both stations of the fork-join part of the network, which are fed by the departures of the first station.
--
--   **Formalization Note** The function takes the backlog $D_{-1}$, the arrival epochs and the service times, and returns $D_j$ at index $j$; the base case $j=0$ uses $D_{-1}$.
-- source:
--   Carmeli, Yom-Tov, Boxma, State-Dependent Estimation of Delay Distributions in Fork-Join Networks, author manuscript (sha256 c8b2002d…9d1c), §2, p.8 (FCFS service policy; single-server FJ stations)

import Mathlib

namespace ForkJoinDelay

/-- **Departure epochs of a single-server FCFS station.**
Carmeli, Yom-Tov, Boxma, *State-Dependent Estimation of Delay Distributions in Fork-Join
Networks*, author manuscript, §2, p.8 ("We assume an FCFS service policy throughout the
network"; "both stations in the FJ part have a single server").

A single server works through the customers already present, finishing them at time `D₀`
(the backlog), and then serves the arriving customers `j = 0, 1, 2, …` in order of their
arrival epochs `A 0 ≤ A 1 ≤ ⋯`, customer `j` needing service time `s j`. Customer `j` starts
service at `max (D_{j-1}) (A j)` and leaves at
`D_j = max (D_{j-1}) (A j) + s j`, with `D_{-1} = D₀`.

**Formalization Note.** The index is shifted by one: `fcfsDeparture D₀ A s j` is `D_j`, and
the base case `j = 0` uses the backlog `D₀` in the role of `D_{-1}`. -/
noncomputable def fcfsDeparture (D₀ : ℝ) (A s : ℕ → ℝ) : ℕ → ℝ
  | 0 => max D₀ (A 0) + s 0
  | n + 1 => max (fcfsDeparture D₀ A s n) (A (n + 1)) + s (n + 1)

end ForkJoinDelay


