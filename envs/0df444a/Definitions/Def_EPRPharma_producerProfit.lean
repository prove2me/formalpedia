-- Prove2me | Definitions.Def_EPRPharma_producerProfit
-- name    : EPRPharma_producerProfit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:09:15.324538+00:00
-- url     : https://prove2.me/theorems/0304b5ed-b20d-4071-8ff9-95311b7ca76e
-- title:
--   The producer's expected profit $\Pi_m$
-- statement:
--   Under model $P$ and policy $y$, a decision $(p,\eta_d,\eta_p)$ gives the producer the expected profit
--
--   $$\Pi_m(p,\eta_d,\eta_p;x_P)=E_{\theta_n}\big[p\,q_p^*(p,\eta_d,\eta_p)\big]-\alpha\eta_d^2-\beta\eta_p^2-C_P(p,\eta_d,\eta_p;x_P).$$
--
--   It is defined from the model itself (the doctor's response and the compliance cost), not from the closed-form optima of the paper's proofs.
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), §3.2, p. 11 (unnumbered display)

import Mathlib
import Definitions.Def_EPRPharma_complianceCost

namespace EPRPharma

/-- **The producer's expected profit Π_m(p, η_d, η_p; x_P).**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), §3.2, p. 11 (unnumbered display):
Π_m(p, η_d, η_p; x_P) = E_{θ_n}[p q*_p(p, η_d, η_p)] − α η_d² − β η_p² − C_P(p, η_d, η_p; x_P).

**Formalization Note.** Defined from the model (the doctor's response `doctorQ` and the compliance
cost), never from the paper's closed-form optima. -/
noncomputable def producerProfit (P : Params) (m : Model) (y : ℝ × ℝ) (d : Decision) : ℝ :=
  E1 (fun θn => d.p * doctorQ P d θn) - P.alpha * d.etaD ^ 2 - P.beta * d.etaP ^ 2
    - complianceCost P m y d

end EPRPharma


