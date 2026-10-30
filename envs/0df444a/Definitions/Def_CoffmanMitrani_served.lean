-- Prove2me | Definitions.Def_CoffmanMitrani_served
-- name    : CoffmanMitrani_served
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:07:11.930926+00:00
-- url     : https://prove2.me/theorems/85054f7b-5670-4484-adf8-57c355cc4acf
-- title:
--   Service received by a job up to time $t$
-- statement:
--   For a schedule $S$, the service received by job $j$ before time $t$ is the Lebesgue measure of the set of times $s \in [0,t)$ at which $S$ serves $j$. The server works at unit rate.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812 (execution intervals)

import Mathlib
import Definitions.Def_CoffmanMitrani_Schedule

namespace CoffmanMitrani

/-- **Service received.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, pp. 811–812 (service of jobs, execution intervals).

`served S j ω t` is the total length of time in `[0, t)` during which schedule `S` serves job `j`,
i.e. the Lebesgue measure of `{s ∈ [0, t) | S ω s = some j}`. The server works at unit rate. -/
noncomputable def served {M : ℕ} (S : Schedule M) (j : Job M) (ω : Omega M) (t : ℝ) : ℝ :=
  (MeasureTheory.volume ({s : ℝ | S ω s = some j} ∩ Set.Ico 0 t)).toReal

end CoffmanMitrani


