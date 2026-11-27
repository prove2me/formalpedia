-- Prove2me | Definitions.Def_SampleMechDesign_Supplement_priceGroupPrices
-- name    : SampleMechDesign_Supplement_priceGroupPrices
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:45:04.35973+00:00
-- url     : https://prove2.me/theorems/74c25465-ea1b-5a2f-833b-410a25c54d56
-- title:
--   Section 5 — the price-group classes $\mathcal M_k$
-- statement:
--   For $k\in[n]$, $\mathcal M_k$ is the class of non-anonymous item-pricing mechanisms with $k$ **price groups**: there is a partition $B_1,\dots,B_k$ of the buyers such that, for all $t\in[k]$, all buyers $j,j'\in B_t$ and all items $i$,
--   $$
--   p_j(e_i)=p_{j'}(e_i).
--   $$
--   The partition is not fixed: $\mathcal M_k$ is the union over all partitions of the buyers into $k$ blocks. These classes form the hierarchy $\mathcal M_1\subseteq\dots\subseteq\mathcal M_n$ on which the structural-risk-minimization bound of Theorem 5.1 is stated.
--
--   **Formalization Note** A partition is given by its block map $g:[n]\to[k]$, existentially quantified, with $g(j)=g(j')\Rightarrow p_j=p_{j'}$. Empty blocks are allowed; for $k\le n$ this gives the same set of price vectors. Prices are nonnegative.
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Section 5, p.17 (PDF p.17)

import Mathlib

namespace SampleMechDesign.Supplement

/-- **Price-group classes `M_k`.** Balcan, Sandholm, Vitercik, arXiv:1705.00243v6, Section 5,
p.17.

`priceGroupPrices n m k` is the set of non-anonymous price vectors `p j i ≥ 0` with `k` price
groups: there is a partition of the buyers into blocks `B_1, …, B_k` such that buyers in one block
see the same price for every item. A partition into `k` blocks is given by its block map
`g : Fin n → Fin k`, and the condition is `g j = g j' → p j = p j'`.

**Formalization Note.** `M_k` is a union over all partitions: nothing fixes the partition, and
`g` is existentially quantified. Empty blocks are allowed, so this is "at most `k` groups"; for
`k ≤ n` (the paper's `k ∈ [n]`) a partition with fewer nonempty blocks can be refined to `k`
blocks with equal prices, so the two readings give the same set. Prices are nonnegative, as for
`itemPricingClass`. -/
def priceGroupPrices (n m k : ℕ) : Set (Fin n → Fin m → ℝ) :=
  {p | (∀ j i, 0 ≤ p j i) ∧ ∃ g : Fin n → Fin k, ∀ j j', g j = g j' → p j = p j'}

end SampleMechDesign.Supplement


