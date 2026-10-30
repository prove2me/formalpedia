-- Prove2me | Definitions.Def_RiskSharingProjects_TimeDependent_projectDelay
-- name    : RiskSharingProjects_TimeDependent_projectDelay
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:15:22.040986+00:00
-- url     : https://prove2.me/theorems/116cc497-fd99-4abc-829c-2c307201113b
-- title:
--   Project delay: the number of delayed tasks
-- statement:
--   For actions $a_1$ of the supplier and $a_0$ of the manufacturer, the **project delay** is the number of periods by which the project's duration exceeds the benchmark. Because the two tasks are in series and each delayed task is delayed by exactly one period,
--
--   $$
--   \mathrm{delay}(a_1,a_0)=\mathbf 1[a_1=D]+\mathbf 1[a_0=D]\in\{0,1,2\}.
--   $$
--
--   This is the "project's duration" whose change under information asymmetry Theorem 6 characterizes.
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), §3, p. 7; Assumption 1(a)-(b), p. 10

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_Action

namespace RiskSharingProjects.TimeDependent

/-- **The project's delay: the number of delayed tasks.**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), §3 (p. 7: "if task i is delayed by one period, firm i saves si in the direct cost; if the
project is delayed by one period, it suffers a penalty p") and Assumption 1(a)–(b), p. 10 (each
stage has one task, each task delayed by at most one period).

`projectDelay a1 a0` is the project's duration relative to the benchmark when the supplier plays
`a1` and the manufacturer plays `a0`: `0`, `1` or `2` periods.

**Formalization Note.** The network is serial, so each delayed task delays the project by one
period and the delay is the number of `delay`s. This is the "project's duration" compared in
Theorem 6 (p. 17), up to the constant benchmark duration. -/
def projectDelay (a1 a0 : Action) : ℕ :=
  (if a1 = Action.delay then 1 else 0) + (if a0 = Action.delay then 1 else 0)

end RiskSharingProjects.TimeDependent


