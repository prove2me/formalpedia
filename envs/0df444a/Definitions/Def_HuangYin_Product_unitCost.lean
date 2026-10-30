-- Prove2me | Definitions.Def_HuangYin_Product_unitCost
-- name    : HuangYin_Product_unitCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:38:11.413793+00:00
-- url     : https://prove2.me/theorems/365c21c1-7acb-49ea-aee3-61c8aaa37358
-- title:
--   Marginal cost of a product
-- statement:
--   The firm's marginal cost of offering product $H$ is $c_H$ and of offering product $L$ is $c_L$.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), §3, p. 7

import Mathlib
import Definitions.Def_HuangYin_Params
import Definitions.Def_HuangYin_Product

namespace HuangYin

/-- **The marginal cost of a product** (§3, p. 7; unnumbered): `cH` for `H`, `cL` for `L`.
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), p. 7: "The marginal cost for offering product m is cm, m = H,L". -/
def Product.unitCost (P : Params) : Product → ℝ
  | .H => P.cH
  | .L => P.cL

end HuangYin


