-- Prove2me | Definitions.Def_CoffmanMitrani_responseTime
-- name    : CoffmanMitrani_responseTime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:09:50.147611+00:00
-- url     : https://prove2.me/theorems/d411d7b3-95f4-470b-bb38-ff0b6e110c08
-- title:
--   Response time $w_i^{(n)}$ (time spent in system)
-- statement:
--   The response time of job $j$ under schedule $S$ is its time spent in system,
--   $$w_j = d_j - a_j,$$
--   the departure time minus the arrival time. It includes the job's own service time.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 811

import Mathlib
import Definitions.Def_CoffmanMitrani_departure
import Definitions.Def_CoffmanMitrani_arrival

namespace CoffmanMitrani

/-- **Response time (time spent in system).**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 811: "let the random variable denoting the time spent in system for the nth arriving
job of class i be wi(n)".

`responseTime S j ω = departure S j ω − arrival ω j`, including the job's own service time. -/
noncomputable def responseTime {M : ℕ} (S : Schedule M) (j : Job M) (ω : Omega M) : ℝ :=
  departure S j ω - arrival ω j

end CoffmanMitrani


