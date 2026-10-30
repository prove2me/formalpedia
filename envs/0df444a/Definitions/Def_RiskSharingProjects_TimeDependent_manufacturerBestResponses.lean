-- Prove2me | Definitions.Def_RiskSharingProjects_TimeDependent_manufacturerBestResponses
-- name    : RiskSharingProjects_TimeDependent_manufacturerBestResponses
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:17:34.250514+00:00
-- url     : https://prove2.me/theorems/e1b94d47-ef07-4c45-9f56-fb8b75b899ac
-- title:
--   The manufacturer's best responses
-- statement:
--   The manufacturer moves after observing the supplier's action. For a manufacturer with saving $s_0$ and penalty shares $p^1_0,p^2_0$, its **best responses** to the supplier's action $a_1$ are
--
--   $$
--   \mathrm{BR}_0(a_1)=\{a_0:\ u_0(a_1,b)\le u_0(a_1,a_0)\ \text{for all actions } b\}.
--   $$
--
--   The set contains both actions exactly when the manufacturer is indifferent; no tie-break is imposed.
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), §4, p. 10; Figure 5b, Appendix p. 1 (PDF 33)

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_Action
import Definitions.Def_RiskSharingProjects_TimeDependent_manufacturerPayoff

namespace RiskSharingProjects.TimeDependent

/-- **The manufacturer's best responses to an observed supplier action.**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), §4, p. 10: "Upon observing the suppliers' actions and their task durations, the manufacturer
then chooses its task duration"; Figure 5b, Appendix p. 1 (PDF 33).

`manufacturerBestResponses s0 p10 p20 a1` is the set of actions `a0` maximizing
`manufacturerPayoff s0 p10 p20 a1 ·` after the supplier's action `a1`.

**Formalization Note.** The set contains both actions exactly at the manufacturer's indifference
points; no tie-break is imposed. Notation: `p11 p21 p10 p20` are the paper's p^1_1, p^2_1, p^1_0, p^2_0 (superscript = period
of project delay, subscript = firm; firm 1 is the supplier, firm 0 the manufacturer). -/
def manufacturerBestResponses (s0 p10 p20 : ℝ) (a1 : Action) : Set Action :=
  {a0 | ∀ b, manufacturerPayoff s0 p10 p20 a1 b ≤ manufacturerPayoff s0 p10 p20 a1 a0}

end RiskSharingProjects.TimeDependent


