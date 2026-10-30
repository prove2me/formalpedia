-- Prove2me | Definitions.Def_CoffmanMitrani_Schedule
-- name    : CoffmanMitrani_Schedule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:06:43.593985+00:00
-- url     : https://prove2.me/theorems/383f17bb-aebe-4a6d-a752-b26b25682372
-- title:
--   Schedules $S(t)$
-- statement:
--   A schedule is a mapping that assigns to each sample point and each time $t$ either a job (the job served at time $t$) or the special value "idle" (the paper's value $0$). Which schedules are admissible scheduling strategies is the definition `IsStrategy`.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812

import Mathlib
import Definitions.Def_CoffmanMitrani_Omega

namespace CoffmanMitrani

/-- **Schedules.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812: "The class of strategies that we consider can be defined as a class of mappings
S(t). The value of a strategy S(t) is either the identifier of the job to be served at time t, or 0
if the server is to be idle."

A schedule assigns to each sample point `ω` and time `t` either `some j` (job `j` is served at time
`t`) or `none` (the paper's value `0`: the server is idle). Which schedules count as scheduling
strategies is `IsStrategy`. -/
abbrev Schedule (M : ℕ) : Type := Omega M → ℝ → Option (Job M)

end CoffmanMitrani


