-- Prove2me | Definitions.Def_HuangYin_cost
-- name    : HuangYin_cost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:34:23.274299+00:00
-- url     : https://prove2.me/theorems/087b3753-bd33-47f7-b399-1334a09829f3
-- title:
--   Expected unit cost of the opaque product
-- statement:
--   If the firm offers product $H$ with probability $\xi$ and product $L$ otherwise, the expected cost of a sold unit of the opaque product is
--
--   $$\xi c_H + (1-\xi) c_L .$$
--
--   This is the cost term in each bracket of the profit (2).
--
--   **Formalization Note** $\xi$ is any real number here; the restriction $\xi\in[0,1]$ is imposed where policies are defined.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), equation (2), p. 11 (the cost term)

import Mathlib
import Definitions.Def_HuangYin_Params

namespace HuangYin

/-- **Expected unit cost of the opaque product** (the bracket of equation (2), p. 11).
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), equation (2), p. 11: the term `ξ cH + (1 − ξ) cL`.
When the firm offers product `H` with probability `ξ` (and `L` otherwise), a sold unit costs
`ξ cH + (1 − ξ) cL` in expectation. -/
def cost (P : Params) (ξ : ℝ) : ℝ := ξ * P.cH + (1 - ξ) * P.cL

end HuangYin


