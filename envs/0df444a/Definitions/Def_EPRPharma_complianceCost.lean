-- Prove2me | Definitions.Def_EPRPharma_complianceCost
-- name    : EPRPharma_complianceCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:08:17.682217+00:00
-- url     : https://prove2.me/theorems/34ddd6ff-f898-4bca-afee-2b1e69df43ce
-- title:
--   The producer's EPR compliance cost $C_P$
-- statement:
--   Write $q_p^*=q_p^*(\theta_n)$ for the doctor's prescription and $q_u^*=\min(\theta_u,q_p^*)$ for the quantity the patient uses. The producer's expected compliance cost is
--
--   $$C_{EC}=E_{\theta_n,\theta_u}\big[k\,r_{EC}\,(q_p^*-q_u^*)\big],\qquad C_{SR}=E_{\theta_n}\big[t\,q_p^*\big].$$
--
--   Under EC he pays the collection cost of the collected share of the unused medicine; under SR he pays the fee on every unit dispensed.
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), §3.3, p. 12 (unnumbered display)

import Mathlib
import Definitions.Def_EPRPharma_Model
import Definitions.Def_EPRPharma_doctorQ
import Definitions.Def_EPRPharma_E1
import Definitions.Def_EPRPharma_E2

namespace EPRPharma

/-- **The producer's expected EPR compliance cost C_P(p, η_d, η_p; x_P).**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), §3.3, p. 12 (unnumbered display):
C_EC = E_{θ_n,θ_u}[k r_EC (q*_p − q*_u)] and C_SR = E_{θ_n}[t q*_p], where q*_u = min(θ_u, q*_p)
is the used quantity (p. 11).

**Formalization Note.** The policy is `y = (r, t)`; EC reads only r = `y.1` and SR only t = `y.2`. -/
noncomputable def complianceCost (P : Params) : Model → ℝ × ℝ → Decision → ℝ
  | .EC, y, d => E2 (fun θn θu => P.k * y.1 * (doctorQ P d θn - min θu (doctorQ P d θn)))
  | .SR, y, d => E1 (fun θn => y.2 * doctorQ P d θn)

end EPRPharma


