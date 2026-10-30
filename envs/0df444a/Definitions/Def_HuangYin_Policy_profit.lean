-- Prove2me | Definitions.Def_HuangYin_Policy_profit
-- name    : HuangYin_Policy_profit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:40:56.635348+00:00
-- url     : https://prove2.me/theorems/ddb6d874-cf2c-40a9-ba17-37cd1cd65c46
-- title:
--   Two-period profit of a selling policy
-- statement:
--   The profit of an opaque policy $(p_1,p_2,\xi_1,\xi_2)$ is $\Pi(\xi_1,\xi_2\mid p_1,p_2)$ from equation (2). The profit of a transparent policy is its transparent two-period profit.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), equation (2), p. 11, and §3.3, p. 11

import Mathlib
import Definitions.Def_HuangYin_opaqueProfit
import Definitions.Def_HuangYin_transparentProfit
import Definitions.Def_HuangYin_Policy

namespace HuangYin

/-- **The total two-period profit of a policy** (equation (2), p. 11, and §3.3, p. 11).
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020). An opaque policy earns `opaqueProfit` (equation (2) with `K = 1`), a transparent one
`transparentProfit` (§3.3). -/
noncomputable def Policy.profit (P : Params) : Policy → ℝ
  | .opaque p1 p2 ξ1 ξ2 => opaqueProfit P p1 p2 ξ1 ξ2
  | .transparent m1 m2 p1 p2 => transparentProfit P m1 m2 p1 p2

end HuangYin


