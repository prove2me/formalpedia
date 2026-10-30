-- Prove2me | Definitions.Def_CoffmanMitrani_departure
-- name    : CoffmanMitrani_departure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:08:49.98357+00:00
-- url     : https://prove2.me/theorems/8664302b-b663-4436-9fb4-86244b0399ca
-- title:
--   Departure time of a job
-- statement:
--   The departure time of job $j$ under schedule $S$ is the first time at which the service it received reaches its requirement:
--   $$d_j = \inf\{t : X_j \le \text{served}_S(j,t)\}.$$
--
--   **Formalization Note** The infimum is taken in the reals; for a scheduling strategy every job is completed almost surely, so the set is nonempty and the infimum is the true departure time except on a null set.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812 (departure times)

import Mathlib
import Definitions.Def_CoffmanMitrani_served
import Definitions.Def_CoffmanMitrani_serviceReq

namespace CoffmanMitrani

/-- **Departure time.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812 ("departure times").

`departure S j ω` is the first time at which the service received by job `j` reaches its
requirement.

**Formalization Note.** Defined as `sInf {t | serviceReq ω j ≤ served S j ω t}`. For a scheduling
strategy every job is completed almost surely (clause 3 of `IsStrategy`), so the set is nonempty and
bounded below (by `0` when the requirement is positive), and the infimum is the true departure time;
the junk value `sInf ∅ = 0` occurs only on a null set. -/
noncomputable def departure {M : ℕ} (S : Schedule M) (j : Job M) (ω : Omega M) : ℝ :=
  sInf {t : ℝ | serviceReq ω j ≤ served S j ω t}

end CoffmanMitrani


