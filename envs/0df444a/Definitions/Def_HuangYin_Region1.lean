-- Prove2me | Definitions.Def_HuangYin_Region1
-- name    : HuangYin_Region1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:43:27.370214+00:00
-- url     : https://prove2.me/theorems/0d10586c-35d0-44e9-bd1f-c9995cc2bfb1
-- title:
--   The region of Proposition 1 (i)
-- statement:
--   Region (i) of Proposition 1 consists of the parameters with
--
--   $$0\le\alpha<\frac{\sqrt{17}-3}{2},\qquad \frac{v_{HL}-c_L}{c_H-c_L}<\frac{4-4\alpha-\alpha^2}{2-\alpha-\alpha^2},\qquad \frac{(1-\alpha)(v_{HL}-c_L)^2}{(4-4\alpha-\alpha^2)(c_H-c_L)}>\max\{v_H-c_H,\,v_L-c_L\}.$$
--
--   On this range of $\alpha$ the quantities $4-4\alpha-\alpha^2$ and $2-\alpha-\alpha^2$ are positive; $(\sqrt{17}-3)/2$ is the positive root of $\alpha^2+3\alpha-2$, where $2-3\alpha-\alpha^2$ changes sign.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), Proposition 1 (i), p. 13

import Mathlib
import Definitions.Def_HuangYin_vHL

namespace HuangYin

/-- **The region of Proposition 1 (i)** (p. 13).
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), Proposition 1 (i), p. 13: "If 0 ≤ α < (√17−3)/2, (vHL−cL)/(cH−cL) < (4−4α−α²)/(2−α−α²)
and (1−α)(vHL−cL)²/((4−4α−α²)(cH−cL)) > max{vH − cH, vL − cL}".

The three conditions are copied term by term. Under them every denominator is positive
(`cH > cL`, and `4 − 4α − α² > 0`, `2 − α − α² > 0` for `0 ≤ α < (√17 − 3)/2`). The conjunct
`0 ≤ α` repeats a standing assumption so that the predicate reads like the page. -/
def Region1 (P : Params) : Prop :=
  0 ≤ P.α ∧ P.α < (Real.sqrt 17 - 3) / 2 ∧
    (vHL P - P.cL) / (P.cH - P.cL) < (4 - 4 * P.α - P.α ^ 2) / (2 - P.α - P.α ^ 2) ∧
    (1 - P.α) * (vHL P - P.cL) ^ 2 / ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL)) >
      max (P.vH - P.cH) (P.vL - P.cL)

end HuangYin


