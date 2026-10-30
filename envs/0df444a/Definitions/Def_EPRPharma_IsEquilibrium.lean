-- Prove2me | Definitions.Def_EPRPharma_IsEquilibrium
-- name    : EPRPharma_IsEquilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:13:46.879744+00:00
-- url     : https://prove2.me/theorems/070b1245-ada9-479c-adb4-8b41d216215a
-- title:
--   Equilibria $(y,d)$ of an EPR model
-- statement:
--   An equilibrium of model $P$ is a pair $(y,d)$ of a policy and a producer decision such that
--
--   1. $y$ is a feasible policy of $P$;
--   2. $d$ is an optimal decision of the producer under $(P,y)$;
--   3. the producer's profit is nonnegative, $\Pi_m^*\ge 0$;
--   4. the planner's surplus is nonnegative, $\Pi_{sp}\ge 0$ (automatic under EC).
--
--   These are the constraints of the planner's problem. When the producer has several optimal decisions (he is indifferent between inducing over-prescription and not), the planner may pair the policy with any of them; this is how the paper's proofs treat the indifference rate $\bar r_{EC}$.
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), §3.3, p. 13 (unnumbered display); proof of Proposition 3, Online Appendix p. 2

import Mathlib
import Definitions.Def_EPRPharma_PolicyFeasible
import Definitions.Def_EPRPharma_IsProducerOptimal
import Definitions.Def_EPRPharma_plannerSurplus

namespace EPRPharma

/-- **Equilibria of model m: a feasible policy with an optimal producer response.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), §3.3, p. 13 (unnumbered display):
the planner maximizes W(y_P) "such that 0 ≤ r_P ≤ 1, t ≥ 0 (if P = SR), Π*_m(x_P) ≥ 0,
Π_sp(y_P) ≥ 0", anticipating the producer's optimal decisions (p. 11).
`IsEquilibrium P m y d` says: y is a feasible policy of model m, d is an optimal decision of the
producer under (m, y), the producer's profit is nonnegative and the planner's surplus is
nonnegative.

**Formalization Note.** When the producer has several optimal decisions (he is indifferent between
inducing over-prescription and not at r̄_EC or t̄) the planner may select any of them: equilibria are
pairs (y, d). This is what the proofs do (Online Appendix p. 2: region (i) for r̄_EC ≤ r_EC and
region (ii) for r_EC ≤ r̄_EC). Under EC the surplus is 0, so its constraint is void. -/
def IsEquilibrium (P : Params) (m : Model) (y : ℝ × ℝ) (d : Decision) : Prop :=
  PolicyFeasible m y ∧ IsProducerOptimal P m y d ∧ 0 ≤ producerProfit P m y d ∧
    0 ≤ plannerSurplus P m y d

end EPRPharma


