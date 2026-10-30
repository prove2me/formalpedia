-- Prove2me | Definitions.Def_HuangYin_OptimalOffer
-- name    : HuangYin_OptimalOffer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:42:57.449795+00:00
-- url     : https://prove2.me/theorems/b7cb7d5e-c9a5-4784-abb1-7ad822cb83ec
-- title:
--   Optimal offering probabilities at fixed prices
-- statement:
--   At fixed opaque prices $p_1,p_2$, the offering probabilities $(x_1,x_2)$ are **optimal** when $x_1,x_2\in[0,1]$ and
--
--   $$\Pi(\xi_1,\xi_2\mid p_1,p_2)\le \Pi(x_1,x_2\mid p_1,p_2)\qquad\text{for all } \xi_1,\xi_2\in[0,1].$$
--
--   This is the notion of "optimal product offering decisions" of the paper's Lemmas 2–4 and of the case (6).
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), Lemmas 2–4, p. 12, and p. 13 after (6)

import Mathlib
import Definitions.Def_HuangYin_opaqueProfit

namespace HuangYin

/-- **Optimal product offering decisions at fixed prices** (Lemmas 2–4 and (6), pp. 12–13).
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), p. 12: "the optimal product offering decisions for the probabilistic selling policy".

`OptimalOffer P p1 p2 x1 x2` holds when `x1, x2 ∈ [0,1]` and `(x1, x2)` maximizes the profit (2)
at the prices `p1, p2` over all offering probabilities `(ξ1, ξ2) ∈ [0,1]²`.

**Formalization Note.** "Optimal" means attaining the maximum, not uniqueness. -/
def OptimalOffer (P : Params) (p1 p2 x1 x2 : ℝ) : Prop :=
  x1 ∈ Set.Icc (0 : ℝ) 1 ∧ x2 ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ y1 ∈ Set.Icc (0 : ℝ) 1, ∀ y2 ∈ Set.Icc (0 : ℝ) 1,
      opaqueProfit P p1 p2 y1 y2 ≤ opaqueProfit P p1 p2 x1 x2

end HuangYin


