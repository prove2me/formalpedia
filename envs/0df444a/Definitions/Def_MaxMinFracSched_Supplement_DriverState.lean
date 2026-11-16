-- Prove2me | Definitions.Def_MaxMinFracSched_Supplement_DriverState
-- name    : MaxMinFracSched_Supplement_DriverState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:20:52.57706+00:00
-- url     : https://prove2.me/theorems/6b4aae62-04ed-4eb2-a6b7-3767f78ceef5
-- title:
--   State of an event-driven scheduler run
-- statement:
--   An event-driven implementation of a scheduler is a persistent real-RAM machine driven through a sequence of **operations**: the arrival of a batch, or an internal event (a job reaching its target, a deadline passing). The driver keeps:
--
--   1. the machine state after the last operation, the time of that operation, the index of the next batch to arrive, and the output of the last operation;
--   2. the **decisions**: one pair $(t,s)$ per operation, meaning that from time $t$ until the next operation the machine serves job $s$ at rate $1$, or idles;
--   3. the **costs**: one pair $(k,\text{steps})$ per operation, where $k$ is the number of jobs that arrived with it ($0$ for an internal event) and steps is its number of executed instructions;
--   4. two flags: the run is finished (no batch left and no event announced), and some operation never halted.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 8.1.7, Scheduling bookkeeping, pp.50–51 (PDF pp.52–53)

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_RealRAM
import Definitions.Def_MaxMinFracSched_Job

namespace MaxMinFracSched

namespace Supplement

open BlottoFPTAS.Main.RealRAM

/-- **The state of an event-driven scheduler run.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 8.1.7, "Scheduling bookkeeping", pp.50–51 (PDF pp.52–53): "Besides arrivals, an event
occurs when a job reaches its target or when a deadline passes."

A persistent real-RAM machine drives a schedule through a sequence of operations (an arrival of a
batch, or an internal event). The driver records:
* `mach`: the machine state after the last operation;
* `time`: the time of the last operation;
* `nextBatch`: the index of the next batch still to arrive;
* `out`: the output of the last operation;
* `segs`: the history of decisions, one `(t, served)` per operation: from time `t` on (until the
  next operation) the machine serves the job `served` at rate `1`, or idles (`none`);
* `ops`: one `(k, steps)` per operation: the number `k` of jobs that arrived with it (`0` for an
  internal event) and the number of executed instructions;
* `finished`: no batch is left and the machine announced no further event;
* `failed`: some operation did not halt. -/
structure DriverState where
  /-- machine state after the last operation -/
  mach : State
  /-- time of the last operation -/
  time : ℝ
  /-- index of the next batch to arrive -/
  nextBatch : ℕ
  /-- output of the last operation -/
  out : List ℝ
  /-- decisions: from time `t` on, serve `served` (or idle) -/
  segs : List (ℝ × Option Job)
  /-- per operation: arriving jobs and executed instructions -/
  ops : List (ℕ × ℕ)
  /-- the run is complete -/
  finished : Bool
  /-- some operation never halted -/
  failed : Bool

end Supplement

end MaxMinFracSched


