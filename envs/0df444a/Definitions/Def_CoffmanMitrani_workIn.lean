-- Prove2me | Definitions.Def_CoffmanMitrani_workIn
-- name    : CoffmanMitrani_workIn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:10:28.628315+00:00
-- url     : https://prove2.me/theorems/22e141b3-2547-452d-ac78-95e20e0dee80
-- title:
--   Work arriving in a time window
-- statement:
--   For times $s,t$ the work arriving in $[s,t)$ is
--   $$\sum_j X_j\, \mathbf 1\{s \le a_j < t\},$$
--   the total service requirement of the jobs that arrive in $[s,t)$.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812; §3, p. 817 (virtual load)

import Mathlib
import Definitions.Def_CoffmanMitrani_arrival
import Definitions.Def_CoffmanMitrani_serviceReq

namespace CoffmanMitrani

/-- **Work brought by the arrivals in a time window.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812 (busy periods), §3, p. 817 ("virtual load").

`workIn ω s t = Σ_j serviceReq ω j · 1{s ≤ arrival ω j < t}`, the total service requirement of the
jobs arriving in `[s, t)`.

**Formalization Note.** A `tsum` over all jobs; almost surely only finitely many jobs arrive in a
bounded window, so it is a finite sum. -/
noncomputable def workIn {M : ℕ} (ω : Omega M) (s t : ℝ) : ℝ :=
  ∑' j : Job M, Set.indicator {j : Job M | s ≤ arrival ω j ∧ arrival ω j < t} (serviceReq ω) j

end CoffmanMitrani


