-- Prove2me | Definitions.Def_EPRPharma_plannerSurplus
-- name    : EPRPharma_plannerSurplus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:11:23.189163+00:00
-- url     : https://prove2.me/theorems/0646abb4-d105-4b8c-b8ba-687cde5a9934
-- title:
--   The social planner's surplus $\Pi_{sp}$
-- statement:
--   Under SR the planner collects the fee and pays for collection at rate $r_{SR}$; her expected surplus is
--
--   $$\Pi_{sp}(r_{SR},t)=E_{\theta_n,\theta_u}\big[t\,q_p-k\,r_{SR}\,(q_p-q_u)\big].$$
--
--   Under EC there is no surplus or deficit: $\Pi_{sp}(r_{EC})=0$. Here $q_p$ is the doctor's prescription and $q_u=\min(\theta_u,q_p)$.
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), §3.3, p. 12 (unnumbered)

import Mathlib
import Definitions.Def_EPRPharma_Model
import Definitions.Def_EPRPharma_doctorQ
import Definitions.Def_EPRPharma_E2

namespace EPRPharma

/-- **The social planner's expected surplus Π_sp.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), §3.3, p. 12: under SR,
Π_sp(r_SR, t) = E_{θ_n,θ_u}[t q_p − k r_SR (q_p − q_u)]; "there is naturally no surplus or deficit for
the social planner under the EC model, i.e., Π_sp(r_EC) = 0".

**Formalization Note.** q_p is the doctor's response `doctorQ` and q_u = min(θ_u, q_p). -/
noncomputable def plannerSurplus (P : Params) : Model → ℝ × ℝ → Decision → ℝ
  | .EC, _, _ => 0
  | .SR, y, d => E2 (fun θn θu => y.2 * doctorQ P d θn
      - P.k * y.1 * (doctorQ P d θn - min θu (doctorQ P d θn)))

end EPRPharma


