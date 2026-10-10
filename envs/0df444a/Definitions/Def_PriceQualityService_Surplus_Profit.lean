-- Prove2me | Definitions.Def_PriceQualityService_Surplus_Profit
-- name    : PriceQualityService_Surplus_Profit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:29.181384+00:00
-- url     : https://prove2.me/theorems/1548c7f1-f8fb-4d4b-a087-e92e83161876
-- title:
--   Markup, total profit (3) and the offer-set profit of problem (10)
-- statement:
--   In the setting of the MNL choice model, producing product $i$ at quality $q_i$ costs $c_iq_i^2$ per unit, and providing service costs $a_i-b_iq_i$ per unit of time over the service duration $t_i$: $a_i$ is the base service cost and $b_i$ the marginal effect of quality on it (of either sign, or zero). The **markup** of product $i$ is
--   $$
--   p_i-c_iq_i^2-t_i(a_i-b_iq_i).
--   $$
--   With the market size normalized to one, the firm's total expected profit (3) is
--   $$
--   \Pi(\mathbf p,\mathbf q,\mathbf t;\mathcal N)=\sum_{i\in\mathcal N}\big[p_i-c_iq_i^2-t_i(a_i-b_iq_i)\big]\cdot d_i(\mathbf p,\mathbf q,\mathbf t;\mathcal N).
--   $$
--   When the firm offers only the products of a set $S\subseteq\mathcal N$ (problem (10)), consumers choose among $S$ and the outside option, and the profit is
--   $$
--   \Pi_S(\mathbf p,\mathbf q,\mathbf t)=\sum_{i\in S}\big[p_i-c_iq_i^2-t_i(a_i-b_iq_i)\big]\cdot\frac{\exp(\alpha_iq_i-p_i+t_is_i)}{1+\sum_{j\in S}\exp(\alpha_jq_j-p_j+t_js_j)} .
--   $$
--   For $S=\mathcal N$ this is $\Pi(\mathbf p,\mathbf q,\mathbf t;\mathcal N)$, and for $S=\emptyset$ it is $0$.
--
--   The profit is the objective of all of the firm's optimization problems compared in the paper.
--
--   **Formalization Note** Problem (10) on p. 20 is printed as $\max_{S\subseteq\mathcal N,\mathbf p,\mathbf t}\Pi(\mathbf p,\mathbf q,\mathbf t;\mathcal N)$; the offer set $S$ is meant, and `offerProfit` encodes it. Qualities are real numbers without sign restriction.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), pp. 8–9 (PDF pp. 8–9), eq. (3); p. 20 (PDF p. 20), problem (10)

import Mathlib
import Definitions.Def_PriceQualityService_Joint_Model

namespace PriceQualityService.Surplus

open Finset

/-- The profit of problem (10), p. 20, when only the products of the offer set `S ⊆ 𝒩` are
offered: the MNL model restricted to `S`,
`∑_{i ∈ S} [p_i − c_i q_i² − t_i(a_i − b_i q_i)] · exp(α_i q_i − p_i + t_i s_i) /
 (1 + ∑_{j ∈ S} exp(α_j q_j − p_j + t_j s_j))`.
For `S = 𝒩` it is `profit`; for `S = ∅` it is `0`. (The paper prints `Π(p, q, t; 𝒩)` in (10);
the offer set `S` is meant.) -/
noncomputable def offerProfit {N : ℕ} (α a b c s : Fin N → ℝ) (S : Finset (Fin N))
    (p q t : Fin N → ℝ) : ℝ :=
  ∑ i ∈ S, PriceQualityService.Joint.markup a b c p q t i * PriceQualityService.Joint.attraction α s p q t i /
    (1 + ∑ j ∈ S, PriceQualityService.Joint.attraction α s p q t j)

end PriceQualityService.Surplus


