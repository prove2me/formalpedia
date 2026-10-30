-- Prove2me | Definitions.Def_HuangYin_Product_value
-- name    : HuangYin_Product_value
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:37:40.208248+00:00
-- url     : https://prove2.me/theorems/0979f606-921b-47d7-8b3d-b7260b88a44e
-- title:
--   Valuation of a product
-- statement:
--   Customers value product $H$ at $v_H$ and product $L$ at $v_L$.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), §3, p. 7

import Mathlib
import Definitions.Def_HuangYin_Params
import Definitions.Def_HuangYin_Product

namespace HuangYin

/-- **The customers' valuation of a product** (§3, p. 7; unnumbered): `vH` for `H`, `vL` for `L`.
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), p. 7: "Product H and L have different valuations for the customers: vH and vL". -/
def Product.value (P : Params) : Product → ℝ
  | .H => P.vH
  | .L => P.vL

end HuangYin


