-- Prove2me | Definitions.Def_PacingComplexity_secondBid
-- name    : PacingComplexity_secondBid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:20.79395+00:00
-- url     : https://prove2.me/theorems/005bbda0-1009-4862-a2b4-d2423870c19c
-- title:
--   Second-highest bid $p_j(\alpha)$ (the price of good $j$)
-- statement:
--   Given values $v_{ij}$ and pacing multipliers $\alpha$, the **second-highest bid** $p_j(\alpha)$ on good $j$ is the second largest element of the list $\alpha_1v_{1j},\dots,\alpha_nv_{nj}$, counted with multiplicity; in particular $p_j(\alpha)=h_j(\alpha)$ when two buyers tie for the highest bid. It equals
--   $$
--   p_j(\alpha)=\max_{i\ne k}\ \min\{\alpha_iv_{ij},\ \alpha_kv_{kj}\}.
--   $$
--   Under the second-price rule every buyer who receives a fraction of good $j$ pays $p_j(\alpha)$ per unit.
--
--   **Formalization Note** Lean uses the displayed max-over-pairs form. With fewer than two buyers the maximum ranges over an empty set and is $0$; instances of the search problem have at least two buyers.
-- source:
--   Chen, Kroer, Kumar, The Complexity of Pacing for Second-Price Auctions, arXiv:2103.13969v2, §2, p.7

import Mathlib

namespace PacingComplexity

/-- **Second-highest bid** `p_j(α)` on good `j` (Chen, Kroer, Kumar, *The Complexity of Pacing for
Second-Price Auctions*, arXiv:2103.13969v2, §2, p.7): "pj(α) is the second largest element among
α1 v1j, . . . , αn vnj (in particular, pj(α) = hj(α) when there is a tie for the highest bid)".
This is the price every buyer pays per unit of good `j`.

**Formalization Note** The second largest element **with multiplicity** is written as the maximum,
over ordered pairs `(i, k)` of distinct buyers, of `min (αi vij) (αk vkj)`: the two largest bids,
taken at distinct buyers, give the second largest value, and no pair does better. A tie for the
highest bid therefore gives `p_j(α) = h_j(α)`. With fewer than two buyers the supremum ranges over
an empty type and is `0`; instances of `ApproxPacing` have at least two buyers. -/
noncomputable def secondBid {N G : Type} (v : N → G → ℝ) (α : N → ℝ) (j : G) : ℝ :=
  ⨆ q : {q : N × N // q.1 ≠ q.2}, min (α q.1.1 * v q.1.1 j) (α q.1.2 * v q.1.2 j)

end PacingComplexity


