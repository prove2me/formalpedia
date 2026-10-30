-- Prove2me | Definitions.Def_EPRPharma_IsProducerOptimal
-- name    : EPRPharma_IsProducerOptimal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:10:37.509845+00:00
-- url     : https://prove2.me/theorems/daaf7952-216f-4852-974c-bc587f70094f
-- title:
--   Optimal decisions of the producer
-- statement:
--   A decision $d$ is optimal for the producer under model $P$ and policy $y$ if it is feasible and
--
--   $$\Pi_m(d;x_P)\ \ge\ \Pi_m(d';x_P)\quad\text{for every feasible decision } d' .$$
--
--   Its profit is then the producer's optimal profit $\Pi_m^*(x_P)$.
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), §3.2, p. 11 (unnumbered display)

import Mathlib
import Definitions.Def_EPRPharma_producerProfit
import Definitions.Def_EPRPharma_DecisionFeasible

namespace EPRPharma

/-- **Optimal decisions of the producer.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), §3.2, p. 11 (unnumbered display):
Π*_m(x_P) = max_{p, η_d, η_p} Π_m(p, η_d, η_p; x_P) such that 0 ≤ η_d ≤ 1, 0 ≤ η_p ≤ 1,
U_d(q*_p) ≥ 0. `IsProducerOptimal P m y d` says that d is feasible and attains this maximum under
model m and policy y. -/
def IsProducerOptimal (P : Params) (m : Model) (y : ℝ × ℝ) (d : Decision) : Prop :=
  DecisionFeasible P d ∧
    ∀ d' : Decision, DecisionFeasible P d' → producerProfit P m y d' ≤ producerProfit P m y d

end EPRPharma


