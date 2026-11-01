-- Prove2me | Definitions.Def_CongestionTaxes_minCost
-- name    : CongestionTaxes_minCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:32:13.128095+00:00
-- url     : https://prove2.me/theorems/3394b0a3-4b08-4345-a083-6ac68db31ec2
-- title:
--   Minimum social cost $\mathrm{MinCost}(G)$
-- statement:
--   For a congestion game $G$, the **social cost** of a profile $a$ is $\mathrm{SC}(a)=\sum_{i=1}^N\sum_{r\in a_i}\ell_r(|a|_r)$, display (1); taxes do not enter it. The **minimum social cost** is
--
--   $$
--   \mathrm{MinCost}(G)=\min_{a\in\mathcal A}\mathrm{SC}(a).
--   $$
--
--   It is the denominator of the price of anarchy (3).
--
--   **Formalization Note** A real infimum over the finite set of profiles, attained when every strategy set is nonempty (the case of every game in the class); SC is the published `CongestionPoA.AsymSum.sumCost`.
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, display (1) and below (3), p.4

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model

namespace CongestionTaxes

/-- The **minimum social cost** `MinCost(G) = min_{a ∈ 𝓐} SC(a)` (Paccagnan, Gairing,
arXiv:2105.07480v2, p.4, below (3)), where `SC(a) = ∑_i ∑_{r ∈ a_i} ℓ_r(|a|_r)` is the social cost (1),
the published `CongestionPoA.AsymSum.sumCost`. Taxes do not enter it (p.5).

**Formalization Note** A real infimum over the finite type of profiles. When every strategy set is
nonempty (as in every game of the class, `InClass`) the type is finite and nonempty and the
infimum is attained, so it is the paper's minimum; on an empty type the real infimum would be `0`,
a case no statement uses. -/
noncomputable def minCost {ι E : Type*} [Fintype ι] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame ι E) : ℝ :=
  ⨅ a : {a : ι → Finset E // CongestionPoA.AsymSum.IsProfile G a},
    CongestionPoA.AsymSum.sumCost G a.1

end CongestionTaxes


