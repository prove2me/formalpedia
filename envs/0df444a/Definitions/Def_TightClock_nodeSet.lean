-- Prove2me | Definitions.Def_TightClock_nodeSet
-- name    : TightClock_nodeSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:08:53.75675+00:00
-- url     : https://prove2.me/theorems/1afe1a03-ffe1-430f-b0ac-6a7660217451
-- title:
--   Set of bidders of a tree node
-- statement:
--   The members of a node in a realized tree are the bidders whose coins are true at all the non-root nodes on the path to it, the node included. In particular "the root (depth 0) is the set $N$ of all bidders", and a child is contained in its parent.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Instance 11, §6.2, p.35 (PDF p.38)

import Mathlib
import Definitions.Def_TightClock_Tree
import Definitions.Def_TightClock_TreeNode
import Definitions.Def_TightClock_ancestor

set_option autoImplicit false

namespace TightClock

/-- The set of bidders of a node: those whose coins are true at every non-root ancestor of the node,
the node included. The root's set is all bidders. Afshinmehr et al., manuscript (STOC 2027 submission),
Instance 11, §6.2, p.35 (PDF 38). -/
def nodeSet {q L : ℕ} (T : Tree q L) (S : TreeNode q L) : Finset (Fin (bidderCount q L)) :=
  Finset.univ.filter (fun i => ∀ k : Fin S.1.val, T (ancestor S k) i = true)

end TightClock


