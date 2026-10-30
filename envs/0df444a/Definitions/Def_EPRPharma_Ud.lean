-- Prove2me | Definitions.Def_EPRPharma_Ud
-- name    : EPRPharma_Ud
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:05:38.869389+00:00
-- url     : https://prove2.me/theorems/886299b3-f085-4bc0-a492-77a20124a80d
-- title:
--   The doctor's utility $U_d(q_p)$
-- statement:
--   Given the producer's decision $(p,\eta_d,\eta_p)$, a doctor treating a patient with need $\theta_n$ who prescribes the quantity $q_p$ obtains
--
--   $$U_d(q_p)=u_p\,\theta_n-p\,q_p+\eta_d\,q_p-o_d\,(1-\eta_p)(q_p-\theta_n).$$
--
--   The first two terms are the altruistic utility (health benefit minus treatment cost), the last two the self-serving utility: the promotional benefit $\eta_d q_p$ and the reputational cost of prescribing beyond the need, attenuated by the promotion $\eta_p$ aimed at patients.
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), §3.1, p. 10 (unnumbered display)

import Mathlib
import Definitions.Def_EPRPharma_Params
import Definitions.Def_EPRPharma_Decision

namespace EPRPharma

/-- **The doctor's utility U_d(q_p).**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), §3.1, p. 10 (unnumbered display):
U_d(q_p) = u_p θ_n − p q_p + η_d q_p − o_d (1 − η_p)(q_p − θ_n), for a patient with need θ_n and a
prescription quantity q_p, given the producer's decision (p, η_d, η_p). The first two terms are the
altruistic utility (health benefit minus treatment cost), the last two the self-serving utility
(promotional benefit minus reputational cost). -/
def Ud (P : Params) (d : Decision) (θn q : ℝ) : ℝ :=
  P.up * θn - d.p * q + d.etaD * q - P.od * (1 - d.etaP) * (q - θn)

end EPRPharma


