-- Prove2me | Definitions.Def_EPRPharma_envDisutility
-- name    : EPRPharma_envDisutility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:11:50.931006+00:00
-- url     : https://prove2.me/theorems/67873824-cdd3-45f3-84a4-d36cf76d03e4
-- title:
--   Expected environmental disutility $E[DU_e]$
-- statement:
--   With collection rate $r_P$, the environmental disutility comes from the metabolized used quantity and the uncollected unused quantity:
--
--   $$DU_e(r_P)=\epsilon_e\big(q_u+(1-r_P)(q_p-q_u)\big),$$
--
--   and the definition is its expectation $E_{\theta_n,\theta_u}[DU_e(r_P)]$, with $q_p$ the doctor's prescription and $q_u=\min(\theta_u,q_p)$.
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), §3.3, p. 13 (unnumbered)

import Mathlib
import Definitions.Def_EPRPharma_doctorQ
import Definitions.Def_EPRPharma_E2

namespace EPRPharma

/-- **Expected total environmental disutility E[DU_e(r_P)].**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), §3.3, p. 13: DU_e(r_P) = ε_e (q_u + (1 − r_P)(q_p − q_u)),
the metabolized used quantity plus the uncollected unused quantity.

**Formalization Note.** r_P is `y.1` for both models; q_p is `doctorQ` and q_u = min(θ_u, q_p). -/
noncomputable def envDisutility (P : Params) (y : ℝ × ℝ) (d : Decision) : ℝ :=
  E2 (fun θn θu => P.epsE * (min θu (doctorQ P d θn)
    + (1 - y.1) * (doctorQ P d θn - min θu (doctorQ P d θn))))

end EPRPharma


