-- Prove2me | Definitions.Def_CoffmanMitrani_History
-- name    : CoffmanMitrani_History
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:13:39.158903+00:00
-- url     : https://prove2.me/theorems/06838f67-3302-426d-b602-8431fccde383
-- title:
--   Information record of a busy period
-- statement:
--   A record of a busy period consists of
--
--   1. the time elapsed since the busy period started;
--   2. for each class $i$ and rank $r$, the arrival time (relative to the start) of the $r$-th class-$i$ job of the busy period, if it has arrived;
--   3. the schedule so far: which job (by class and rank) was served at each elapsed time before now, which determines all execution intervals;
--   4. for each class and rank, the departure time (relative to the start) of that job, if it has departed.
--
--   This is the information that Assumption 2 allows a scheduling decision to depend on: "arrival times, departure times, execution intervals, and (priority) class indices which apply to jobs waiting, being served, or having been served during $B$ up to time $t$".
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812, Assumption 2

import Mathlib

namespace CoffmanMitrani

/-- **The information record of a busy period.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812, Assumption 2: "If t falls within busy period B, then the domain of S(t) is
restricted to those arrival times, departure times, execution intervals, and (priority) class
indices which apply to jobs waiting, being served, or having been served during B up to time t."

A record contains, with all times measured from the start of the busy period and every job named by
its class and its rank within the busy period:
1. `elapsed` — the time elapsed since the busy period started;
2. `arrivals (i, r)` — the arrival time of the `r`-th class-`i` job of the busy period, if it has
   arrived by now, else `none`;
3. `schedule s` — which job was served at elapsed time `s`, for `0 ≤ s < elapsed` (else `none`);
   this records all execution intervals so far;
4. `departures (i, r)` — the departure time of that job, if it has departed by now, else `none`. -/
structure History (M : ℕ) where
  elapsed : ℝ
  arrivals : Fin M × ℕ → Option ℝ
  schedule : ℝ → Option (Fin M × ℕ)
  departures : Fin M × ℕ → Option ℝ

end CoffmanMitrani


