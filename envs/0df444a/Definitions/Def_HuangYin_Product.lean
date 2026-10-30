-- Prove2me | Definitions.Def_HuangYin_Product
-- name    : HuangYin_Product
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:37:07.950517+00:00
-- url     : https://prove2.me/theorems/b80b1015-2b75-45bf-9168-431a1b0f02e8
-- title:
--   The product versions $H$ and $L$
-- statement:
--   The firm sells two versions of a product: the high version $H$ and the low version $L$.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), §3, p. 7

import Mathlib

namespace HuangYin

/-- **The two product versions** `H` and `L` (§3, p. 7; unnumbered).
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), p. 7: "A firm sells a product of two different versions (i.e., product H and product L)". -/
inductive Product
  | H
  | L
  deriving DecidableEq

end HuangYin


