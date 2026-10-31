-- Prove2me | Definitions.Def_SharedControl_S
-- name    : SharedControl_S
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:08:38.036508+00:00
-- url     : https://prove2.me/theorems/d2735a78-037a-4af4-a650-841e417c20cb
-- title:
--   Surplus under shared control, $S(z) = q[z + (1-z)P_s]\,2\pi_g$ (eq. (3))
-- statement:
--   Let $z$ be the probability that the stakeholder observes $r$. Under shared control a bad proposal is never implemented; a good one is implemented with surplus $2\pi_g$ when the stakeholder is informed, and with probability $\Pr[m_g \ge t_s] = P_s$ when it is not. The **joint expected surplus under shared control** is equation (3) of the paper,
--
--   $$
--   S(z) \;=\; q\,\bigl[z + (1 - z)\Pr[m_g \ge t_s]\bigr]\, 2\pi_g .
--   $$
--
--   Proposition 8 compares how $S$ and the undivided-control surplus $\tilde U$ vary with $z$.
--
--   **Formalization Note** $S$ is defined for every real $z$; the theorems restrict to $z \in [0,1]$.
-- source:
--   Meyersson Milgrom, Milgrom, Singh, When Should Control Be Shared?, Management Science (2023), doi:10.1287/mnsc.2022.4356, §2.1, eq. (3), p.4

import Mathlib
import Definitions.Def_SharedControl_Model
import Definitions.Def_SharedControl_Feasible
import Definitions.Def_SharedControl_ts
import Definitions.Def_SharedControl_Ps

namespace SharedControl

/-- Meyersson Milgrom, Milgrom, Singh, *When Should Control Be Shared?*, Management Science
(2023), doi:10.1287/mnsc.2022.4356, §2.1, eq. (3), p.4 (PDF p.5): the joint expected surplus
under shared control, as a function of the probability `z` that the stakeholder observes `r`.
"However, with probability 1 − z, the stakeholder is uninformed. In this case, the proposal is
implemented only if mg ≥ ts. The joint expected surplus under shared control is, therefore,
S ≡ q[z + (1 − z)Pr[mg ≥ ts]]2πg. (3)"

**Formalization Note.** `Pr[mg ≥ ts]` is `SharedControl.Ps M`. The function is defined for
every real `z`; the paper's `z` is a probability, and the theorems restrict to `z ∈ [0, 1]`. -/
noncomputable def S {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (z : ℝ) : ℝ :=
  M.q * (z + (1 - z) * Ps M) * (2 * M.πg)

end SharedControl


