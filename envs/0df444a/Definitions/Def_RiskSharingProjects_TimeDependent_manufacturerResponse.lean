-- Prove2me | Definitions.Def_RiskSharingProjects_TimeDependent_manufacturerResponse
-- name    : RiskSharingProjects_TimeDependent_manufacturerResponse
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:21:35.213079+00:00
-- url     : https://prove2.me/theorems/72be8819-a60a-41b0-abed-847d3907c524
-- title:
--   A manufacturer type's response to the supplier's action
-- statement:
--   A manufacturer of type $\theta=(s_0',p^{1\prime}_0,p^{2\prime}_0)$ observes the supplier's action $a_1$ and responds with
--
--   $$
--   r_\theta(a_1)=\begin{cases}D,& u_0^\theta(a_1,K)<u_0^\theta(a_1,D),\\ K,&\text{otherwise,}\end{cases}
--   $$
--
--   where $u_0^\theta$ is the manufacturer payoff with parameters $\theta$. On each class of Assumption 2 the comparison is strict, so $r_\theta(a_1)$ is the unique best response: low-saving types keep after both actions, medium-saving types delay after $K$ and keep after $D$, high-saving types delay after both.
--
--   **Formalization Note** The tie-break (keep at indifference) only affects types outside the three classes, a null set for every supplier belief.
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), §5, p. 15; proof of Theorem 5, Appendix p. 5 (PDF 37)

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_Action
import Definitions.Def_RiskSharingProjects_TimeDependent_manufacturerPayoff

namespace RiskSharingProjects.TimeDependent

/-- **A manufacturer type's response to the supplier's action.**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), §5, p. 15: "After observing the suppliers' actions, the manufacturer takes its action";
proof of Theorem 5, Appendix p. 5 (PDF 37): "If s0 < p^1_0 < p^2_0, the manufacturer will choose
"keep" … If p^1_0 < s0 < p^2_0, the manufacturer will choose "delay" … If p^1_0 < p^2_0 < s0, the
manufacturer will choose "delay"".

`manufacturerResponse θ a1` is `delay` if a manufacturer of type `θ = (s0', p^1_0', p^2_0')`
strictly prefers delaying after the supplier's action `a1`, and `keep` otherwise.

**Formalization Note.** This is the type's best response; it is unique on each of the three
classes of Assumption 2, since there each comparison is strict. The tie-break (keep at
indifference) only affects types outside those classes, a null set for every `SupplierBelief`. -/
noncomputable def manufacturerResponse (θ : ℝ × ℝ × ℝ) (a1 : Action) : Action :=
  if manufacturerPayoff θ.1 θ.2.1 θ.2.2 a1 Action.keep <
      manufacturerPayoff θ.1 θ.2.1 θ.2.2 a1 Action.delay then Action.delay else Action.keep

end RiskSharingProjects.TimeDependent


