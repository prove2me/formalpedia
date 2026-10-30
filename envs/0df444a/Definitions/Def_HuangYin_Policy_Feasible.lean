-- Prove2me | Definitions.Def_HuangYin_Policy_Feasible
-- name    : HuangYin_Policy_Feasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:40:00.65866+00:00
-- url     : https://prove2.me/theorems/8d06f3d8-1506-41e7-8fad-85ef54bb7bad
-- title:
--   Feasible selling policies
-- statement:
--   An opaque policy $(p_1,p_2,\xi_1,\xi_2)$ is feasible when $\xi_1,\xi_2\in[0,1]$ and $p_1\le v_{HL}$. Every transparent policy is feasible.
--
--   **Formalization Note** The paper works with prices from the grid $\{v_L,v_{HL}\}$ (Lemma 1). The feasible set allows every second-period price and every first-period price up to $v_{HL}$, which contains the grid. First-period prices above $v_{HL}$ are excluded: nobody buys in period 1 then, but the profit (2) would still let second-period anecdotes come from period 1 and be $H$ with probability $\xi_1$, so (2) does not model that case.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), §3, p. 7 (ξt ∈ [0,1]), and §4, p. 11 (prices)

import Mathlib
import Definitions.Def_HuangYin_vHL
import Definitions.Def_HuangYin_Policy

namespace HuangYin

/-- **Feasible policies** (§3, p. 7, and §4, p. 11; unnumbered).
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), p. 7: "the firm offers product H at a probability ξt ∈ [0,1] in any period t".

An opaque policy is feasible when `ξ1, ξ2 ∈ [0,1]` and the first-period price is at most `vHL`;
every transparent policy is feasible.

**Formalization Note.** The paper optimizes over the grid `p1, p2 ∈ {vL, vHL}` (Lemma 1, p. 10;
§4, p. 11). Here `p2` is any real and `p1` any real `≤ vHL`, which contains the grid. A
first-period price above `vHL` is excluded: then nobody buys in period 1, yet the period-2
anecdote probability `α ξ1 + (1 − α) ξ2` of (2) still draws period-1 anecdotes that are `H` with
probability `ξ1`, so the model of (2) does not describe that case. -/
def Policy.Feasible (P : Params) : Policy → Prop
  | .opaque p1 _ ξ1 ξ2 => ξ1 ∈ Set.Icc (0 : ℝ) 1 ∧ ξ2 ∈ Set.Icc (0 : ℝ) 1 ∧ p1 ≤ vHL P
  | .transparent _ _ _ _ => True

end HuangYin


