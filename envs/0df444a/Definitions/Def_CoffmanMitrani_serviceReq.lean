-- Prove2me | Definitions.Def_CoffmanMitrani_serviceReq
-- name    : CoffmanMitrani_serviceReq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:05:32.763656+00:00
-- url     : https://prove2.me/theorems/ff302e69-5339-4544-ae2d-1d8066a3cea5
-- title:
--   Service requirement of a job
-- statement:
--   The service requirement $X_j$ of job $j$ is the total amount of service it needs; under the model's law it is exponential with parameter $\mu_i$ for a class-$i$ job.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 811

import Mathlib
import Definitions.Def_CoffmanMitrani_Omega

namespace CoffmanMitrani

/-- **Service requirement of a job.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 811: jobs of class `i` "have service times distributed exponentially with parameter μi".

`serviceReq ω j` is the total amount of service job `j` requires. -/
def serviceReq {M : ℕ} (ω : Omega M) (j : Job M) : ℝ := ω.2.1 j

end CoffmanMitrani


