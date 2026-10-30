-- Prove2me | Definitions.Def_EPRPharma_NonnegOptimalProfit
-- name    : EPRPharma_NonnegOptimalProfit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:19:53.15186+00:00
-- url     : https://prove2.me/theorems/ed4f6839-e5a7-4232-a131-709ea2df73ee
-- title:
--   The policy maintains a non-negative producer profit
-- statement:
--   A policy $y$ of model $P$ maintains a non-negative producer profit if the producer has an optimal decision under $(P,y)$ and its profit is nonnegative: $\Pi_m^*(x_P)\ge 0$. This is the qualifier of Proposition 1, "for any $r_{EC}\in[0,1]$ (for any $t\ge 0$) that maintains a non-negative producer profit".
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), Proposition 1, p. 15

import Mathlib
import Definitions.Def_EPRPharma_IsProducerOptimal

namespace EPRPharma

/-- **The policy maintains a non-negative producer profit.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), Proposition 1, p. 15: "for any
r_EC ∈ [0,1] (for any t ≥ 0) that maintains a non-negative producer profit".
`NonnegOptimalProfit P m y` says that the producer has an optimal decision under (m, y) and his
optimal profit Π*_m is nonnegative. -/
def NonnegOptimalProfit (P : Params) (m : Model) (y : ℝ × ℝ) : Prop :=
  ∃ d, IsProducerOptimal P m y d ∧ 0 ≤ producerProfit P m y d

end EPRPharma


