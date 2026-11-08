-- Prove2me | Definitions.Def_TightClock_Tree
-- name    : TightClock_Tree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:05:18.14485+00:00
-- url     : https://prove2.me/theorems/15848aa3-2566-4f73-93d7-ad79afbd4826
-- title:
--   Realization of the hierarchical tree
-- statement:
--   A realization of Instance 11 is recorded by its coins: for each non-root node and each bidder, one Boolean. A bidder is a member of a node when all her coins along the path from the root to that node are true.
--
--   **Formalization Note** "Each child contains every member of $S$ independently with probability $a$" is encoded by independent coins, for all bidders at all nodes. A coin of a bidder absent from the parent has no effect, and summing it out returns the law on the page. Under this encoding the generate-one-node-at-a-time argument of Lemma 6.9 is independence in a product space.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Instance 11, §6.2, p.35 (PDF p.38)

import Mathlib
import Definitions.Def_TightClock_NonrootNode
import Definitions.Def_TightClock_bidderCount

set_option autoImplicit false

namespace TightClock

/-- A realized tree of Instance 11, given by its coins: for every non-root node and every bidder, a coin
`T D i`. The bidder belongs to the node when her coins are heads at the node and at all its ancestors.
Afshinmehr et al., manuscript (STOC 2027 submission), Instance 11, §6.2, p.35 (PDF 38).

**Formalization Note** This encodes "each child contains every member of S independently with probability
a" as independent coins. A coin of a bidder who is not a member of the parent has no effect, and summing it
out returns the page's law. -/
abbrev Tree (q L : ℕ) : Type := NonrootNode q L → Fin (bidderCount q L) → Bool

end TightClock


