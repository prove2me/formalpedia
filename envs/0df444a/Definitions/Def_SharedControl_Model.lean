-- Prove2me | Definitions.Def_SharedControl_Model
-- name    : SharedControl_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:06.918988+00:00
-- url     : https://prove2.me/theorems/8adf6304-76f4-49da-a9ba-c46dd1bd3c2f
-- title:
--   The shared-control model: payoffs $m_i = \pi_i + r$, $s_i = \pi_i - r$
-- statement:
--   A firm has two risk-neutral parties, a **manager** who generates a proposal and a **stakeholder** with an interest in whether it is implemented. With probability $q$ the state is good ($g$) and the project increases joint surplus; otherwise it is bad ($b$). The project redistributes a random amount $r$ of wealth from the stakeholder to the manager, and in state $i \in \{g, b\}$ the payoffs are
--
--   $$
--   m_i = \pi_i + r, \qquad s_i = \pi_i - r .
--   $$
--
--   The data of the model are a probability space $(\Omega, P)$, the redistribution $r : \Omega \to \mathbb R$, the half surpluses $\pi_g$, $\pi_b$, the probability $q$ of the good state, and the bounds $r_l$, $r_h$ of the support of $r$.
--
--   This structure carries the data of every statement of the mission; the paper's assumptions on it are the separate predicate of standing assumptions.
--
--   **Formalization Note** The probability $z$ that the stakeholder observes $r$ is not part of the model: it is the variable of the surplus functions $S$ and $\tilde U$, and the equilibrium transfer $t_s$ does not depend on it.
-- source:
--   Meyersson Milgrom, Milgrom, Singh, When Should Control Be Shared?, Management Science (2023), doi:10.1287/mnsc.2022.4356, §2, p.3

import Mathlib

open MeasureTheory

namespace SharedControl

/-- Meyersson Milgrom, Milgrom, Singh, *When Should Control Be Shared?*, Management Science
(2023), doi:10.1287/mnsc.2022.4356, §2, p.3 (PDF p.4): the data of the model. "With probability
q, the state is “good” (g), and the project increases joint surplus; otherwise, the state is
“bad” (b), and the project is unproductive. In state i, the manager’s payoff is mi = πi + r, and
the stakeholder’s payoff is si = πi − r, where πg > 0 and πb ≤ 0. The proposal redistributes a
positive amount r of wealth from the stakeholder to the manager. We assume that r has a
continuous distribution with support on [rl, rh], where 0 ≤ rl < rh < ∞."

The fields are the probability space `P` on `Ω`, the redistribution `r : Ω → ℝ`, the half
surpluses `πg`, `πb`, the probability `q` of the good state, and the support bounds `rl`, `rh`.
The payoffs are `m_i = πi + r ω` and `s_i = πi − r ω` (pointwise in `ω`).

**Formalization Note.** The structure carries the data only; the paper's assumptions on it
(probability measure, measurability of `r`, continuous law supported on `[rl, rh]`, signs of the
parameters) are the separate predicate `SharedControl.Standing`. The probability `z` that the
stakeholder observes `r` is not a field: it is the variable of the surplus functions
`SharedControl.S` and `SharedControl.Utilde`, and the equilibrium transfer `t_s` does not depend
on it. -/
structure Model (Ω : Type*) [MeasurableSpace Ω] where
  /-- The probability measure on the sample space. -/
  P : Measure Ω
  /-- The redistribution `r` from the stakeholder to the manager. -/
  r : Ω → ℝ
  /-- Half the joint surplus of a good project, `πg`. -/
  πg : ℝ
  /-- Half the joint surplus of a bad project, `πb`. -/
  πb : ℝ
  /-- The probability `q` that the state is good. -/
  q : ℝ
  /-- The lower end `rl` of the support of `r`. -/
  rl : ℝ
  /-- The upper end `rh` of the support of `r`. -/
  rh : ℝ

end SharedControl


