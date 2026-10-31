-- Prove2me | Definitions.Def_SharedControl_Utilde
-- name    : SharedControl_Utilde
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:43.902245+00:00
-- url     : https://prove2.me/theorems/4a716229-35d5-4f40-908d-954d69c77961
-- title:
--   Surplus under undivided control with limits on transfers, $\tilde U = 2[q\pi_g + (1-q)\Pr[m_b \ge 0]\pi_b]$ (eq. (7))
-- statement:
--   When control is undivided and transfers are disallowed, the manager implements a proposal whenever her payoff $m_i$ is nonnegative. The joint surplus is $2\pi_g$ in the good state, $2\pi_b$ in the bad state when $m_b \ge 0$, and zero otherwise, so the **joint expected surplus under undivided control with limits on transfers** is equation (7) of the paper,
--
--   $$
--   \tilde U \;=\; 2\bigl[q\pi_g + (1 - q)\Pr[m_b \ge 0]\,\pi_b\bigr], \qquad m_b = \pi_b + r .
--   $$
--
--   It does not involve the stakeholder's information, which is the content of the second half of Proposition 8.
--
--   **Formalization Note** $\tilde U$ takes the probability $z$ that the stakeholder observes $r$ as an argument that it does not use, so that "no change as $z$ increases" is a statement about a function of $z$; its value is the right-hand side of (7) for every $z$.
-- source:
--   Meyersson Milgrom, Milgrom, Singh, When Should Control Be Shared?, Management Science (2023), doi:10.1287/mnsc.2022.4356, §4, eq. (7), p.8

import Mathlib
import Definitions.Def_SharedControl_Model

open MeasureTheory

namespace SharedControl

/-- Meyersson Milgrom, Milgrom, Singh, *When Should Control Be Shared?*, Management Science
(2023), doi:10.1287/mnsc.2022.4356, §4, eq. (7), p.8 (PDF p.9): the joint expected surplus under
undivided control with limits on transfers. "Let ˜U denote the joint expected surplus when
control is undivided. The joint surplus is 2πg if the state is good, 2πb if the state is bad and
mb ≥ 0, and zero otherwise. So, ˜U = 2[qπg + (1 − q)Pr[mb ≥ 0]πb]. (7)" Here `mb = πb + r`.

**Formalization Note.** `Ũ` is given an argument `z` (the probability that the stakeholder
observes `r`) that it does not use, so that Proposition 8's "no change in the benefit of
undivided control" as `z` increases is a statement about a function of `z`; the value is the
right-hand side of (7) for every `z`. The probability is the real number
`P.real {ω | 0 ≤ πb + r ω}`. -/
noncomputable def Utilde {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (_z : ℝ) : ℝ :=
  2 * (M.q * M.πg + (1 - M.q) * M.P.real {ω | 0 ≤ M.πb + M.r ω} * M.πb)

end SharedControl


