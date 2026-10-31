-- Prove2me | Definitions.Def_CrowdLastMile_sumCheapest
-- name    : CrowdLastMile_sumCheapest
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:21:41.596952+00:00
-- url     : https://prove2.me/theorems/4044d86e-cc2d-4d0f-9b78-f5da0603d0a3
-- title:
--   Sum of the $N$ smallest means (order statistics)
-- statement:
--   Let $\mu_1,\dots,\mu_{\mathbb N}$ be real numbers with order statistics $\mu_{(1)}\le\mu_{(2)}\le\dots\le\mu_{(\mathbb N)}$. This definition is the sum of the $N$ smallest of them:
--
--   $$
--   \sum_{i=1}^{N}\mu_{(i)} .
--   $$
--
--   It is the opportunity-cost term of the cheapest $N$ crowd drivers in Lemma 1 and in the participation constraint of Problem (14).
--
--   **Formalization Note** The order statistics come from sorting the multiset of the means, and the sum is that of the first $N$ entries of the sorted list. It is not defined as a minimum over subsets of size $N$, because the equality of the two is part of Lemma 1.
-- source:
--   Fatehi–Wagner, Crowdsourcing Last-Mile Deliveries, SSRN 3434625, Lemma 1, p.12

import Mathlib

namespace CrowdLastMile

/-- The sum `∑_{i=1}^N μ_(i)` of the `N` smallest of the means `μ_1, …, μ_ℕ`, where
`μ_(1) ≤ μ_(2) ≤ ⋯ ≤ μ_(ℕ)` are their order statistics. Fatehi–Wagner, Crowdsourcing Last-Mile
Deliveries, SSRN 3434625, Lemma 1, p.12.

**Formalization Note.** The order statistics are obtained by sorting the multiset of the means
(`Multiset.sort`); the sum is that of the first `N` entries of the sorted list. It is deliberately
not defined as a minimum over subsets of size `N`: the equality of the two is part of Lemma 1. -/
noncomputable def sumCheapest {pop : ℕ} (μ : Fin pop → ℝ) (N : ℕ) : ℝ :=
  (((Finset.univ.val.map μ).sort (· ≤ ·)).take N).sum

end CrowdLastMile


