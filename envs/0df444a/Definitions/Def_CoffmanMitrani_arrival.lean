-- Prove2me | Definitions.Def_CoffmanMitrani_arrival
-- name    : CoffmanMitrani_arrival
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:04:48.39704+00:00
-- url     : https://prove2.me/theorems/0baecdfe-7211-4775-b713-9c7525d0488b
-- title:
--   Arrival time of a job
-- statement:
--   The arrival time of the $n$-th job of class $i$ is the sum of the first $n$ interarrival times of class $i$ (counting the time from $0$ to the first arrival):
--   $$a_{(i,n)} = \sum_{m \le n} \tau_{(i,m)}.$$
--
--   **Formalization Note** Classes are indexed $0,\dots,M-1$ (`Fin M`) and the jobs of a class $0,1,2,\dots$; the paper's class $i$ and $n$-th job are the Lean class $i-1$ and job $n-1$.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 811

import Mathlib
import Definitions.Def_CoffmanMitrani_Omega

namespace CoffmanMitrani

/-- **Arrival time of a job.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 811 (Poisson streams), p. 814 ("start in the idle state at t = 0").

`arrival ω (i, n) = Σ_{m ≤ n} ω.1 (i, m)`: the `n`-th (0-based) class-`i` arrival happens after the
first `n + 1` class-`i` interarrival times. -/
def arrival {M : ℕ} (ω : Omega M) (j : Job M) : ℝ :=
  ∑ m ∈ Finset.range (j.2 + 1), ω.1 (j.1, m)

end CoffmanMitrani


