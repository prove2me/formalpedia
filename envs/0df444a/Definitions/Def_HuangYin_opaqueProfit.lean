-- Prove2me | Definitions.Def_HuangYin_opaqueProfit
-- name    : HuangYin_opaqueProfit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:36:51.805088+00:00
-- url     : https://prove2.me/theorems/f81b59ff-59c0-4488-a712-5b9de26161e1
-- title:
--   Two-period profit under probabilistic selling, equation (2)
-- statement:
--   Under probabilistic selling the firm sells the opaque product at price $p_t$ in period $t$ and delivers product $H$ with probability $\xi_t$. The two-period profit is
--
--   $$\Pi(\xi_1,\xi_2\mid p_1,p_2)=\gamma(p_1,\xi_1)\,[p_1-\xi_1c_H-(1-\xi_1)c_L]+\gamma\big(p_2,\alpha\xi_1+(1-\alpha)\xi_2\big)\,[p_2-\xi_2c_H-(1-\xi_2)c_L],$$
--
--   where $\gamma$ is the one-anecdote purchasing fraction. A first-period anecdote is $H$ with probability $\xi_1$. A second-period anecdote comes from period 1 with probability $\alpha$ and is then $H$ with probability $\xi_1$, and otherwise it comes from period 2 and is $H$ with probability $\xi_2$.
--
--   At the four price pairs in $\{v_L,v_{HL}\}^2$ this gives the paper's displays (3)–(6).
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), equation (2), p. 11, and §3.2, pp. 9–10

import Mathlib
import Definitions.Def_HuangYin_cost
import Definitions.Def_HuangYin_demand

namespace HuangYin

/-- **The firm's two-period profit under probabilistic (opaque) selling** (equation (2), p. 11).
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), p. 11:
"Π(ξ1, ξ2 | p1, p2) = γ1(p1, ξ1)[p1 − ξ1cH − (1 − ξ1)cL] + γ2(p2, ξ2, ξ1)[p2 − ξ2cH − (1 − ξ2)cL].  (2)"
with γ1, γ2 the purchasing fractions of Lemma 1, here for `K = 1`.

In period 1 a customer's anecdote comes from period 1, so it is `H` with probability `ξ1`. In
period 2 an anecdote comes from period 1 with probability `α` (then it is `H` with probability
`ξ1`) and from period 2 otherwise (then `H` with probability `ξ2`), so it is `H` with probability
`α ξ1 + (1 − α) ξ2` (§3.2, pp. 9–10).

**Formalization Note.** Prices and offering probabilities are arbitrary reals here; the feasible
set (`ξt ∈ [0,1]`, `p1 ≤ vHL`) is imposed in `Policy.Feasible` and `OptimalOffer`. -/
noncomputable def opaqueProfit (P : Params) (p1 p2 ξ1 ξ2 : ℝ) : ℝ :=
  demand P p1 ξ1 * (p1 - cost P ξ1) + demand P p2 (P.α * ξ1 + (1 - P.α) * ξ2) * (p2 - cost P ξ2)

end HuangYin


