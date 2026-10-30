-- Prove2me | Definitions.Def_EPRPharma_socDisutility
-- name    : EPRPharma_socDisutility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:12:20.13701+00:00
-- url     : https://prove2.me/theorems/d5676f74-6516-490e-a4e0-72bf3f537874
-- title:
--   Expected social disutility $E[DU_s]$
-- statement:
--   The social disutility (misuse, abuse, poisonings) comes from the uncollected unused medicine:
--
--   $$DU_s(r_P)=\epsilon_s\,(1-r_P)(q_p-q_u),$$
--
--   and the definition is its expectation $E_{\theta_n,\theta_u}[DU_s(r_P)]$, with $q_p$ the doctor's prescription and $q_u=\min(\theta_u,q_p)$.
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), §3.3, p. 13 (unnumbered)

import Mathlib
import Definitions.Def_EPRPharma_doctorQ
import Definitions.Def_EPRPharma_E2

namespace EPRPharma

/-- **Expected total social disutility E[DU_s(r_P)].**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), §3.3, p. 13: DU_s(r_P) = ε_s (1 − r_P)(q_p − q_u), the
social cost of the uncollected unused medicine.

**Formalization Note.** r_P is `y.1` for both models; q_p is `doctorQ` and q_u = min(θ_u, q_p). -/
noncomputable def socDisutility (P : Params) (y : ℝ × ℝ) (d : Decision) : ℝ :=
  E2 (fun θn θu => P.epsS * (1 - y.1) * (doctorQ P d θn - min θu (doctorQ P d θn)))

end EPRPharma


