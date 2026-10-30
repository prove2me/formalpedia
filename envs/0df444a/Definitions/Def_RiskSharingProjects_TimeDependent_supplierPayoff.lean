-- Prove2me | Definitions.Def_RiskSharingProjects_TimeDependent_supplierPayoff
-- name    : RiskSharingProjects_TimeDependent_supplierPayoff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:16:10.77579+00:00
-- url     : https://prove2.me/theorems/56d12140-f4bf-46fb-b51e-38fe19c02430
-- title:
--   The supplier's payoff (Figure 5b)
-- statement:
--   The supplier saves $s_1$ in direct cost if it delays its task and pays its share of the delay penalty:
--
--   $$
--   u_1(a_1,a_0)=s_1\,\mathbf 1[a_1=D]-\mathrm{pen}\big(p^1_1,p^2_1;\mathrm{delay}(a_1,a_0)\big).
--   $$
--
--   This reproduces the supplier column of Figure 5b: $u_1(K,K)=0$, $u_1(K,D)=-p^1_1$, $u_1(D,K)=s_1-p^1_1$, $u_1(D,D)=s_1-p^1_1-p^2_1$.
--
--   Throughout, $p^k_i$ is the penalty of the $k$-th period of project delay borne by firm $i$; firm $1$ is the supplier and firm $0$ the manufacturer.
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), Figure 5b, Appendix p. 1 (PDF 33); §4.1, p. 12

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_Action
import Definitions.Def_RiskSharingProjects_TimeDependent_projectDelay
import Definitions.Def_RiskSharingProjects_TimeDependent_delayPenalty

namespace RiskSharingProjects.TimeDependent

/-- **The supplier's payoff in the basic model with time-dependent cost (Figure 5b).**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), Figure 5b, Appendix p. 1 (PDF 33); §4.1, p. 12. The supplier (firm 1) saves `s1` in direct
cost if it delays its task and bears its share of the delay penalty:
`supplierPayoff s1 p11 p21 a1 a0 = (s1 if a1 = delay, else 0) − delayPenalty p11 p21 (projectDelay a1 a0)`.

This gives Figure 5b's supplier column: `[K,K] 0`, `[K,D] −p^1_1`, `[D,K] s1 − p^1_1`,
`[D,D] s1 − p^1_1 − p^2_1`.

Notation: `p11 p21 p10 p20` are the paper's p^1_1, p^2_1, p^1_0, p^2_0 (superscript = period
of project delay, subscript = firm; firm 1 is the supplier, firm 0 the manufacturer). -/
noncomputable def supplierPayoff (s1 p11 p21 : ℝ) (a1 a0 : Action) : ℝ :=
  (if a1 = Action.delay then s1 else 0) - delayPenalty p11 p21 (projectDelay a1 a0)

end RiskSharingProjects.TimeDependent


