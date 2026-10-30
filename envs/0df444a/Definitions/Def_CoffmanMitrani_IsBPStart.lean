-- Prove2me | Definitions.Def_CoffmanMitrani_IsBPStart
-- name    : CoffmanMitrani_IsBPStart
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:11:38.173381+00:00
-- url     : https://prove2.me/theorems/95214586-0b88-4ff6-b7ce-7e60bf822729
-- title:
--   Job opening a busy period
-- statement:
--   Job $j_0$ opens a busy period if it arrives to an empty system: for every $s \le a_{j_0}$ the work arriving in $[s, a_{j_0})$ is at most $a_{j_0} - s$. Equivalently, the virtual load (total unfinished work) just before $a_{j_0}$ is zero.
--
--   **Formalization Note** Busy periods are defined from the arrival and service data. Under Assumption 1 the server is never idle while work is present, so the busy periods are the same for every scheduling strategy.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812 (busy and idle periods)

import Mathlib
import Definitions.Def_CoffmanMitrani_workIn

namespace CoffmanMitrani

/-- **Job opening a busy period.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812: "Busy periods and idle periods have the usual definitions; i.e. t falls within a
busy period if and only if at time t there exists in the system at least one job requiring further
service; otherwise, t falls within an idle period."

`IsBPStart ω j0` says that job `j0` arrives to an empty system: for every `s ≤ arrival ω j0`, the work
arriving in `[s, arrival ω j0)` is at most `arrival ω j0 − s`, i.e. the virtual load (unfinished
work) just before `arrival ω j0` is zero.

**Formalization Note.** Busy and idle periods are defined from the data, without reference to a
strategy: under Assumption 1 (no idling while work is present) the server works at unit rate
whenever work is present, so busy periods are the same for every strategy (p. 813: "the stationary
distribution of busy period length remains the same"). The system is empty at time `0`. -/
def IsBPStart {M : ℕ} (ω : Omega M) (j0 : Job M) : Prop :=
  ∀ s ≤ arrival ω j0, workIn ω s (arrival ω j0) ≤ arrival ω j0 - s

end CoffmanMitrani


