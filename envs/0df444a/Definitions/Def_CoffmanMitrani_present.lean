-- Prove2me | Definitions.Def_CoffmanMitrani_present
-- name    : CoffmanMitrani_present
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:07:59.984645+00:00
-- url     : https://prove2.me/theorems/ab98ff99-e4c5-4429-b8f5-bf597fd781c4
-- title:
--   Job requiring further service
-- statement:
--   Job $j$ is present (in the system and requiring further service) at time $t$ under schedule $S$ if it has arrived by time $t$ and the service it received before $t$ is still smaller than its service requirement:
--   $$a_j \le t \quad\text{and}\quad \text{served}_S(j,t) < X_j.$$
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812 (busy periods)

import Mathlib
import Definitions.Def_CoffmanMitrani_served
import Definitions.Def_CoffmanMitrani_arrival
import Definitions.Def_CoffmanMitrani_serviceReq

namespace CoffmanMitrani

/-- **A job requiring further service.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812: "t falls within a busy period if and only if at time t there exists in the system
at least one job requiring further service".

`present S j ω t` holds when job `j` has arrived by time `t` and the service it received in
`[0, t)` is still less than its requirement. -/
def present {M : ℕ} (S : Schedule M) (j : Job M) (ω : Omega M) (t : ℝ) : Prop :=
  arrival ω j ≤ t ∧ served S j ω t < serviceReq ω j

end CoffmanMitrani


