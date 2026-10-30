-- Prove2me | Definitions.Def_EPRPharma_OPStrictlyMoreProfitable
-- name    : EPRPharma_OPStrictlyMoreProfitable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:19:14.823986+00:00
-- url     : https://prove2.me/theorems/9e926250-d8ac-4c3c-a2bd-da6fad7a8695
-- title:
--   Over-prescription is strictly more profitable for the producer
-- statement:
--   Under model $P$ and policy $y$, the producer gains a higher profit by inducing over-prescription if some feasible decision $d$ that induces over-prescription satisfies
--
--   $$\Pi_m(d';x_P)<\Pi_m(d;x_P)\quad\text{for every feasible decision } d' \text{ that does not.}$$
--
--   This is the conclusion of Propositions 1 and 2.
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), Propositions 1–2, pp. 15–16

import Mathlib
import Definitions.Def_EPRPharma_producerProfit
import Definitions.Def_EPRPharma_DecisionFeasible
import Definitions.Def_EPRPharma_OverPrescribes

namespace EPRPharma

/-- **The producer gains a higher profit by inducing over-prescription.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), Propositions 1 and 2, pp. 15–16:
"the producer gains a higher profit by inducing over-prescription".
`OPStrictlyMoreProfitable P m y` says that some feasible decision inducing over-prescription earns
strictly more, under (m, y), than every feasible decision that does not. -/
def OPStrictlyMoreProfitable (P : Params) (m : Model) (y : ℝ × ℝ) : Prop :=
  ∃ d, DecisionFeasible P d ∧ OverPrescribes P d ∧
    ∀ d', DecisionFeasible P d' → ¬ OverPrescribes P d' →
      producerProfit P m y d' < producerProfit P m y d

end EPRPharma


