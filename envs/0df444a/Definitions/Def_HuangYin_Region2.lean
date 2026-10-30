-- Prove2me | Definitions.Def_HuangYin_Region2
-- name    : HuangYin_Region2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:43:51.936987+00:00
-- url     : https://prove2.me/theorems/13ded4c5-c90d-4f7d-86bf-59541cc5406a
-- title:
--   The region of Proposition 1 (ii)
-- statement:
--   Region (ii) of Proposition 1 consists of the parameters with
--
--   $$\frac{\sqrt{17}-3}{2}\le\alpha\le1,\qquad \frac{v_{HL}-c_L}{c_H-c_L}<\frac{2}{1+\alpha},\qquad \frac{(1+\alpha)^2(v_{HL}-c_L)^2}{8(c_H-c_L)}>\max\{v_H-c_H,\,v_L-c_L\}.$$
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), Proposition 1 (ii), p. 13

import Mathlib
import Definitions.Def_HuangYin_vHL

namespace HuangYin

/-- **The region of Proposition 1 (ii)** (p. 13).
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), Proposition 1 (ii), p. 13: "If (√17−3)/2 ≤ α ≤ 1, (vHL−cL)/(cH−cL) < 2/(1+α) and
(1+α)²(vHL−cL)²/(8(cH−cL)) > max{vH − cH, vL − cL}".

The three conditions are copied term by term; `α ≤ 1` repeats a standing assumption so that the
predicate reads like the page. -/
def Region2 (P : Params) : Prop :=
  (Real.sqrt 17 - 3) / 2 ≤ P.α ∧ P.α ≤ 1 ∧
    (vHL P - P.cL) / (P.cH - P.cL) < 2 / (1 + P.α) ∧
    (1 + P.α) ^ 2 * (vHL P - P.cL) ^ 2 / (8 * (P.cH - P.cL)) > max (P.vH - P.cH) (P.vL - P.cL)

end HuangYin


