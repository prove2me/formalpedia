-- Prove2me | Definitions.Def_CommissionsSubscriptions_minCost
-- name    : CommissionsSubscriptions_minCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:25:09.811696+00:00
-- url     : https://prove2.me/theorems/633be59c-ca46-4c00-80f9-df787a6b3dc7
-- title:
--   Cheapest effective price $\min_{i':(i',j)\in E}\{(1+\gamma^b_j)p_{i'}+c_{i'}\}$
-- statement:
--   Given fees $(\gamma,\mu)$ and prices $p$, the **cheapest effective price** for type-$j$ buyers is
--   $$\min_{i':(i',j)\in E}\bigl\{(1+\gamma^b_j)\,p_{i'}+c_{i'}\bigr\},$$
--   the smallest total cost (payment plus disutility) at which a type-$j$ buyer can trade with a compatible seller. It appears in the demand condition (2b) and the routing condition (2d) of Definition 1.
--
--   **Formalization Note** Defined as an infimum over the neighbours of $j$. The neighbour set is finite, and nonempty for every buyer type under the degree hypothesis in `MarketHyp`, so the infimum is the minimum.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), Definition 1, (2b) and (2d), p. 9

import Mathlib
import Definitions.Def_CommissionsSubscriptions_Market
import Definitions.Def_CommissionsSubscriptions_Fees

namespace CommissionsSubscriptions

/-- **The cheapest effective price for type-`j` buyers,
`min_{i′:(i′,j)∈E} {(1 + γ^b_j) p_{i′} + c_{i′}}`.**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), Definition 1, (2b) and (2d), p. 9.

**Formalization Note (Reading 7).** An infimum over the neighbour subtype `{i // (i, j) ∈ E}`.
That subtype is finite, so the infimum is the minimum as soon as it is nonempty, which the
degree-at-least-one hypothesis of `MarketHyp` guarantees for every buyer type. (For an empty
neighbour set ℝ's `iInf` would return `0`; that case is excluded by `MarketHyp`.) -/
noncomputable def minCost {S B : Type} (M : Market S B) (f : Fees S B) (p : S → ℝ) (j : B) : ℝ :=
  ⨅ i : {i : S // (i, j) ∈ M.E}, ((1 + f.gb j) * p i + M.c i)

end CommissionsSubscriptions


