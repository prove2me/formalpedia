-- Prove2me | Definitions.Def_CoffmanMitrani_history__a0cb5b
-- name    : CoffmanMitrani_history
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:14:21.889701+00:00
-- url     : https://prove2.me/theorems/a0cb5b3d-f43c-44a9-890a-5fa1be8d2f5b
-- title:
--   The record of the current busy period at time $t$
-- statement:
--   For a schedule $S$, a sample point, a job $j_0$ opening a busy period and a time $t$ in it, the record at time $t$ contains the arrivals up to time $t$, the schedule on $[a_{j_0}, t)$ and the departures up to time $t$ of the jobs of this busy period, all times measured from $a_{j_0}$ and every job named by its class and rank within the busy period.
--
--   The record contains no service requirement except through departures that have already occurred, no future arrival, and no information about earlier busy periods (neither the absolute time nor absolute job indices).
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812, Assumption 2

import Mathlib
import Definitions.Def_CoffmanMitrani_History
import Definitions.Def_CoffmanMitrani_Schedule
import Definitions.Def_CoffmanMitrani_classOffset
import Definitions.Def_CoffmanMitrani_served
import Definitions.Def_CoffmanMitrani_departure
import Definitions.Def_CoffmanMitrani_serviceReq

namespace CoffmanMitrani

open Classical in
/-- **The record of a busy period seen at time `t`.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812, Assumption 2.

For a schedule `S`, a sample point `ω`, the job `j0` that opens a busy period and a time `t` in that
busy period, `history S ω j0 t` is the record (see `History`) of arrivals up to time `t`, of the
schedule on `[arrival ω j0, t)`, and of departures up to time `t`, with times measured from
`b = arrival ω j0` and the class-`i` job `(i, classOffset ω j0 i + r)` relabelled as `(i, r)`.

**Formalization Note.** The record contains no service requirement except through departures that
have already happened, no future arrival, and nothing from earlier busy periods (not even the
absolute time `b` or the absolute job indices). -/
noncomputable def history {M : ℕ} (S : Schedule M) (ω : Omega M) (j0 : Job M) (t : ℝ) :
    History M where
  elapsed := t - arrival ω j0
  arrivals := fun p =>
    if arrival ω (p.1, classOffset ω j0 p.1 + p.2) ≤ t then
      some (arrival ω (p.1, classOffset ω j0 p.1 + p.2) - arrival ω j0)
    else none
  schedule := fun s =>
    if 0 ≤ s ∧ s < t - arrival ω j0 then
      (S ω (arrival ω j0 + s)).map (fun j => (j.1, j.2 - classOffset ω j0 j.1))
    else none
  departures := fun p =>
    if serviceReq ω (p.1, classOffset ω j0 p.1 + p.2) ≤
        served S (p.1, classOffset ω j0 p.1 + p.2) ω t then
      some (departure S (p.1, classOffset ω j0 p.1 + p.2) ω - arrival ω j0)
    else none

end CoffmanMitrani


