-- Prove2me | Definitions.Def_CoffmanMitrani_seed
-- name    : CoffmanMitrani_seed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:06:09.67304+00:00
-- url     : https://prove2.me/theorems/cdb11882-1aea-4181-956b-4afc27b66ab6
-- title:
--   Random seeds attached to a job
-- statement:
--   The seed sequence of job $j$ is the sequence $u_j(0), u_j(1), \dots$ of uniform random numbers attached to $j$. A randomized strategy uses the seeds of the job that opens the current busy period.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812, Assumption 3

import Mathlib
import Definitions.Def_CoffmanMitrani_Omega

namespace CoffmanMitrani

/-- **Seeds of a job.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812, Assumption 3 (randomized strategies).

`seed ω j` is the sequence of uniform seeds attached to job `j`; a strategy uses the seeds of the
job that opens the current busy period (see `IsStrategy`). -/
def seed {M : ℕ} (ω : Omega M) (j : Job M) : ℕ → unitInterval := ω.2.2 j

end CoffmanMitrani


