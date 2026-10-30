-- Prove2me | Definitions.Def_EPRPharma_welfare
-- name    : EPRPharma_welfare
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:13:17.22055+00:00
-- url     : https://prove2.me/theorems/c22939b1-c20e-4ceb-9a0e-d2fa85801d67
-- title:
--   Total expected welfare $W$
-- statement:
--   For model $P$, policy $y_P$ and producer decision $d$, the total expected welfare is
--
--   $$W=E\big[U_d(q_p^*)+\Pi_m+\Pi_{sp}-DU_e(r_P)-DU_s(r_P)\big],$$
--
--   the doctor's utility (which contains the patient's health benefit), the producer's profit and the planner's surplus, minus the environmental and social disutilities. At an equilibrium $d$ is optimal for the producer, so $\Pi_m$ is $\Pi_m^*$.
--
--   **Formalization Note** The doctor's term is $E_{\theta_n}[U_d(q_p^*(\theta_n))]$; the usage $\theta_u$ does not enter $U_d$.
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), §3.3, p. 13 (unnumbered display)

import Mathlib
import Definitions.Def_EPRPharma_producerProfit
import Definitions.Def_EPRPharma_plannerSurplus
import Definitions.Def_EPRPharma_envDisutility
import Definitions.Def_EPRPharma_socDisutility

namespace EPRPharma

/-- **Total expected welfare W(y_P).**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), §3.3, p. 13 (unnumbered display):
W(y_P) = E[U_d(q*_p) + Π*_m(x_P) + Π_sp(y_P) − DU_e(r_P) − DU_s(r_P)].
`welfare P m y d` is this quantity when the producer's decision is d.

**Formalization Note.** The doctor's term is E_{θ_n}[U_d(q*_p(θ_n))] (θ_u does not enter U_d). The
producer's term is the profit of the decision d; at an equilibrium d is optimal, so it is Π*_m. -/
noncomputable def welfare (P : Params) (m : Model) (y : ℝ × ℝ) (d : Decision) : ℝ :=
  E1 (fun θn => Ud P d θn (doctorQ P d θn)) + producerProfit P m y d + plannerSurplus P m y d
    - envDisutility P y d - socDisutility P y d

end EPRPharma


