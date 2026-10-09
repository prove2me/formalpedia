-- Prove2me | Definitions.Def_SLPricing_Resp_P2Star
-- name    : SLPricing_Resp_P2Star
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T10:07:39.787177+00:00
-- url     : https://prove2.me/theorems/e64f2e7a-5b06-470b-bde9-f5bfa0d61967
-- title:
--   Equation (6), p. 20 — the responsive second-period price $p_2^*(q_u,\bar x)$
-- statement:
--   Under responsive pricing, let $\bar x\in[0,1]$ be the mass of consumers remaining in the market in period 2 (the types $[0,\bar x)$), let $q_u$ be the realized posterior mean quality and $c$ the unit cost. Equation (6) of Lemma 3 defines the second-period price
--   $$p_2^*(q_u,\bar x) = \begin{cases} c & \text{if } q_u \le c - \bar x,\\[2pt] \dfrac{q_u + c + \bar x}{2} & \text{if } c-\bar x < q_u \le c+\bar x,\\[2pt] q_u & \text{if } q_u > c+\bar x.\end{cases}$$
--   In the first regime the firm sells nothing (exit), in the second it sells to a fraction of the remaining consumers, and in the third it clears the market.
--
--   That this price is optimal for the firm is Lemma 3, a separate theorem; the definition only records the formula.
--
--   **Formalization Note** The Lean function takes the arguments in the order $(c, q_u, \bar x)$. It is defined by the same three-case formula for all real arguments; the restriction $\bar x\in[0,1]$ is a hypothesis of the theorems that use it. In the exit regime the paper's convention $p_2^*=c$ is kept: there no price earns positive profit, and at $p_2^*=c$ no consumer buys (the paper's "exit", p. 20).
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Lemma 3 (i), equation (6), p. 20

import Mathlib

namespace SLPricing.Resp

/-- Lemma 3 (i), equation (6), p. 20: the firm's second-period price under responsive pricing,
given the realized posterior mean `q = q_u`, the unit cost `c` and the remaining mass `xbar = x̄`:
`c` if `q ≤ c − x̄` (exit), `(q + c + x̄)/2` if `c − x̄ < q ≤ c + x̄`, and `q` if `q > c + x̄`. -/
noncomputable def p2Star (c q xbar : ℝ) : ℝ :=
  if q ≤ c - xbar then c else if q ≤ c + xbar then (q + c + xbar) / 2 else q

end SLPricing.Resp


