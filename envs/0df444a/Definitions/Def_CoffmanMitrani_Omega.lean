-- Prove2me | Definitions.Def_CoffmanMitrani_Omega
-- name    : CoffmanMitrani_Omega
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:03:39.903648+00:00
-- url     : https://prove2.me/theorems/7db0109f-3075-4f19-a112-e18f169416e1
-- title:
--   Sample space of the queueing model
-- statement:
--   A sample point records, for every job $j$:
--
--   1. the interarrival time preceding $j$ in the arrival stream of its class;
--   2. the service requirement of $j$;
--   3. a sequence of random seeds $u_j(0), u_j(1), \dots \in [0,1]$.
--
--   The seeds are the source of randomness for randomized scheduling strategies: during a busy period a strategy may use the seeds of the job that opens that busy period, and no others.
--
--   **Formalization Note** Randomized sequencing rules (Assumption 3) are encoded as deterministic functions of uniform seeds, which can generate any probability law of decisions.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, pp. 811–812 (model; Assumption 3)

import Mathlib
import Definitions.Def_CoffmanMitrani_Job

namespace CoffmanMitrani

/-- **The canonical sample space.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 811: "Jobs of class i arrive in a Poisson stream at rate λi and have service times
distributed exponentially with parameter μi … The arrival and service processes for all job classes
are mutually independent."; §1, p. 812, Assumption 3: "A mapping S(t) may be deterministic or it may
be governed by some probability law whose parameters are restricted to those in Assumption 2 above."

A sample point `ω : Omega M` has three coordinates:
1. `ω.1 j` — the interarrival time preceding job `j = (i, n)` in the class-`i` stream (for `n = 0`,
   the time from `0` to the first class-`i` arrival);
2. `ω.2.1 j` — the service requirement of job `j`;
3. `ω.2.2 j` — a sequence of random seeds in `[0, 1]` attached to job `j`; the seeds of the job that
   opens a busy period are the randomization source available to a strategy during that busy period.

**Formalization Note.** The space is canonical (its law is `Data.P`). Randomization of a strategy
(Assumption 3) is encoded as a deterministic function of the seeds; every probability law on
decisions can be generated from i.i.d. uniform seeds. Seeds are attached to jobs, and a busy period
uses only the seeds of the job that opens it, so different busy periods use independent seeds. -/
abbrev Omega (M : ℕ) : Type := (Job M → ℝ) × (Job M → ℝ) × (Job M → ℕ → unitInterval)

end CoffmanMitrani


