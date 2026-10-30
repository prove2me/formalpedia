-- Prove2me | Definitions.Def_RiskSharingProjects_TimeDependent_manufacturerPayoff
-- name    : RiskSharingProjects_TimeDependent_manufacturerPayoff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:16:48.608277+00:00
-- url     : https://prove2.me/theorems/6dc9bf47-7b7e-41e6-8224-6f5cfbaad6a8
-- title:
--   The manufacturer's payoff (Figure 5b)
-- statement:
--   The manufacturer saves $s_0$ in direct cost if it delays its task and pays its share of the delay penalty:
--
--   $$
--   u_0(a_1,a_0)=s_0\,\mathbf 1[a_0=D]-\mathrm{pen}\big(p^1_0,p^2_0;\mathrm{delay}(a_1,a_0)\big).
--   $$
--
--   This reproduces the manufacturer column of Figure 5b: $u_0(K,K)=0$, $u_0(K,D)=s_0-p^1_0$, $u_0(D,K)=-p^1_0$, $u_0(D,D)=s_0-p^1_0-p^2_0$.
--
--   Throughout, $p^k_i$ is the penalty of the $k$-th period of project delay borne by firm $i$; firm $1$ is the supplier and firm $0$ the manufacturer.
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), Figure 5b, Appendix p. 1 (PDF 33); §4.1, p. 12

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_Action
import Definitions.Def_RiskSharingProjects_TimeDependent_projectDelay
import Definitions.Def_RiskSharingProjects_TimeDependent_delayPenalty

namespace RiskSharingProjects.TimeDependent

/-- **The manufacturer's payoff in the basic model with time-dependent cost (Figure 5b).**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), Figure 5b, Appendix p. 1 (PDF 33); §4.1, p. 12. The manufacturer (firm 0) saves `s0` in
direct cost if it delays its task and bears its share of the delay penalty:
`manufacturerPayoff s0 p10 p20 a1 a0 = (s0 if a0 = delay, else 0) − delayPenalty p10 p20 (projectDelay a1 a0)`.

This gives Figure 5b's manufacturer column: `[K,K] 0`, `[K,D] s0 − p^1_0`, `[D,K] −p^1_0`,
`[D,D] s0 − p^1_0 − p^2_0`.

Notation: `p11 p21 p10 p20` are the paper's p^1_1, p^2_1, p^1_0, p^2_0 (superscript = period
of project delay, subscript = firm; firm 1 is the supplier, firm 0 the manufacturer). -/
noncomputable def manufacturerPayoff (s0 p10 p20 : ℝ) (a1 a0 : Action) : ℝ :=
  (if a0 = Action.delay then s0 else 0) - delayPenalty p10 p20 (projectDelay a1 a0)

end RiskSharingProjects.TimeDependent


