-- Prove2me | Definitions.Def_TightClock_toNode
-- name    : TightClock_toNode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:04:37.214126+00:00
-- url     : https://prove2.me/theorems/2e766bd1-c102-4b37-a753-db7b4accd0f7
-- title:
--   Non-root node as a tree node
-- statement:
--   The inclusion of the nodes of depth at least $1$ in the nodes of the tree.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Instance 11, §6.2, p.35 (PDF p.38)

import Mathlib
import Definitions.Def_TightClock_NonrootNode
import Definitions.Def_TightClock_TreeNode

set_option autoImplicit false

namespace TightClock

/-- A non-root node, seen as a node of the tree. -/
def toNode {q L : ℕ} (D : NonrootNode q L) : TreeNode q L :=
  ⟨⟨D.1.val + 1, Nat.succ_lt_succ D.1.isLt⟩, D.2⟩

end TightClock


