-- Prove2me | Definitions.Def_SharedControl_Feasible
-- name    : SharedControl_Feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:51.225156+00:00
-- url     : https://prove2.me/theorems/f93d43eb-70d5-4a10-aad1-8eca6dbf62b8
-- title:
--   Nonnegative transfers satisfying Inequality (1), $E[s_g + t \mid m_g \ge t] \ge 0$
-- statement:
--   Under shared control, when the stakeholder is uninformed about $r$, the manager offers a transfer $t$ exactly when $m_g \ge t$, and the stakeholder accepts if it is profitable in expectation given that the offer is made. A transfer $t$ is **feasible** if $t \ge 0$ and it satisfies Inequality (1) of the paper,
--
--   $$
--   E[s_g + t \mid m_g \ge t] \;=\; E[\pi_g - r + t \mid \pi_g + r \ge t] \;\ge\; 0 .
--   $$
--
--   The equilibrium transfer $t_s$ is the smallest feasible transfer.
--
--   **Formalization Note** The conditional expectation given the event $A = \{m_g \ge t\}$ is the integral against the conditional probability measure $P(\cdot \mid A)$. Since it is undefined when $\Pr[A] = 0$ (Lean's conditional measure is then zero and the integral $0$), feasibility also requires $\Pr[m_g \ge t] > 0$; this does not change the smallest feasible transfer.
-- source:
--   Meyersson Milgrom, Milgrom, Singh, When Should Control Be Shared?, Management Science (2023), doi:10.1287/mnsc.2022.4356, §2.1, eq. (1), p.4

import Mathlib
import Definitions.Def_SharedControl_Model

open MeasureTheory ProbabilityTheory

namespace SharedControl

/-- Meyersson Milgrom, Milgrom, Singh, *When Should Control Be Shared?*, Management Science
(2023), doi:10.1287/mnsc.2022.4356, §2.1, eq. (1), p.4 (PDF p.5): a nonnegative transfer `t`
satisfies Inequality (1). "In any pure equilibrium, there is the smallest nonnegative transfer t
that the stakeholder will accept and subsequently not veto the project. The manager then offers
t if and only if mg ≥ t. At equilibrium, it must be profitable for the stakeholder to accept the
offer and refrain from vetoing, so E[sg + t | mg ≥ t] ≥ 0. (1)"

Here `mg = πg + r` and `sg = πg − r`, so (1) reads
`E[πg − r + t | πg + r ≥ t] ≥ 0`.

**Formalization Note.** The conditional expectation given the event `A = {mg ≥ t}` is the
integral against the conditional probability measure `P[|A]` (`ProbabilityTheory.cond`). It is
undefined on a null event, and `cond` returns the zero measure there, which would make every
`t ≥ πg + rh` satisfy (1) by a junk value; so feasibility also asks `0 < P(mg ≥ t)`. This does
not change the smallest feasible transfer (milestone `SharedControl.ts_isLeast`). Under
`SharedControl.Standing` the integrand is integrable (`r` is almost surely bounded). -/
def Feasible {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (t : ℝ) : Prop :=
  0 ≤ t ∧ 0 < M.P {ω | t ≤ M.πg + M.r ω} ∧
    0 ≤ ∫ ω, (M.πg - M.r ω + t) ∂(M.P[|{ω | t ≤ M.πg + M.r ω}])

end SharedControl


