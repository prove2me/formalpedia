-- Prove2me | Definitions.Def_RiskSharingProjects_TimeDependent_Action
-- name    : RiskSharingProjects_TimeDependent_Action
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:14:45.795791+00:00
-- url     : https://prove2.me/theorems/b72d0caa-7da9-4787-8a5b-015b0039bc4a
-- title:
--   Actions keep ($K$) and delay ($D$)
-- statement:
--   In the basic model of Song, Zhao and Xu, a project consists of two tasks performed in series: the supplier (firm $1$) performs the first, the manufacturer (firm $0$) the second. Each task can be kept to its benchmark duration or delayed by at most one period (Assumption 1(a)–(b)). An **action** is therefore one of two values: *keep* ($K$) or *delay* ($D$).
--
--   This two-element type carries every strategy, payoff and equilibrium of the mission.
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), §3, pp. 7–9; Assumption 1(a)-(b), p. 10; Figure 5b, Appendix p. 1 (PDF 33)

import Mathlib

namespace RiskSharingProjects.TimeDependent

/-- **A firm's action: keep to the benchmark duration or delay its task by one period.**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), §3 (pp. 7–9) and Assumption 1(a)–(b), p. 10: "each task can be delayed by at most one period
relative to the benchmark"; Figure 5b (Appendix p. 1 = PDF 33) labels the two branches `K`
("keep") and `D` ("delay").

**Formalization Note.** Assumption 1(b) (the basic model with time-dependent cost) is encoded by
the game itself: a serial network with one task per stage, the supplier (firm 1) acting first and
the manufacturer (firm 0) second, each choosing `keep` or `delay`. -/
inductive Action
  | keep
  | delay
  deriving DecidableEq, Repr

instance : Fintype Action :=
  ⟨{Action.keep, Action.delay}, fun a => by cases a <;> simp⟩

end RiskSharingProjects.TimeDependent


