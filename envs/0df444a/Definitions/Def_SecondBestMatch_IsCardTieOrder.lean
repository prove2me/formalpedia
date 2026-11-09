-- Prove2me | Definitions.Def_SecondBestMatch_IsCardTieOrder
-- name    : SecondBestMatch_IsCardTieOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:47.922002+00:00
-- url     : https://prove2.me/theorems/e075d326-21dc-4dfc-afc9-abaed35230eb
-- title:
--   Cardinality-first tie-breaking order on $\mathcal F$
-- statement:
--   A rank $\mathrm{rank}:\mathcal F\to\mathbb N$ is a **cardinality-first tie-breaking order** if it is injective on $\mathcal F$ and every matching of smaller cardinality has smaller rank.
--
--   With such a rank, the tie-broken first-best matching `firstBest m rank t` is the paper's $M^*(t)$: among welfare-maximizing matchings, first minimize cardinality, then apply a fixed total order on $\mathcal F$. Every fixed total order on $\mathcal F$, refined by cardinality, is such a rank, and every such rank arises this way. The convention is report independent, and it makes every edge of $M^*(t)$ have strictly positive surplus.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 2.3, p.9

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- A tie-breaking rank that orders by cardinality first (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §2.3, p.9): `rank` is injective
on `ℱ` (a strict total order on `ℱ`) and every matching of smaller cardinality has smaller rank.

**Formalization Note** With such a rank, `MatchingGFT.TightE.firstBest m rank t` is the paper's
`M*(t)`: "first minimize cardinality among welfare maximizers, and then apply the fixed total
order". Every total order on `ℱ`, refined by cardinality, is such a rank, and every such rank
arises this way. -/
def IsCardTieOrder {B S : Type*} (m : Market B S) (rank : Finset (B × S) → ℕ) : Prop :=
  IsTieOrder m rank ∧ ∀ M ∈ m.family, ∀ M' ∈ m.family, M.card < M'.card → rank M < rank M'

end SecondBestMatch


