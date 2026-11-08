-- Prove2me | Definitions.Def_TightClock_ancestor
-- name    : TightClock_ancestor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:04:59.477907+00:00
-- url     : https://prove2.me/theorems/1e526d34-8707-4dc2-a5d1-6b2c5d67cfda
-- title:
--   Non-root ancestors of a node
-- statement:
--   For a node $S$ and $k$ below its depth, the ancestor of $S$ at depth $k+1$: the node whose path is the first $k+1$ choices of the path of $S$. For $k+1$ equal to the depth of $S$, this is $S$ itself.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Instance 11, §6.2, p.35 (PDF p.38)

import Mathlib
import Definitions.Def_TightClock_NonrootNode
import Definitions.Def_TightClock_TreeNode

set_option autoImplicit false

namespace TightClock

/-- The ancestor at depth `k + 1` of a node `S` at depth greater than `k`, possibly `S` itself. -/
def ancestor {q L : ℕ} (S : TreeNode q L) (k : Fin S.1.val) : NonrootNode q L :=
  ⟨⟨k.val, Nat.lt_of_lt_of_le k.isLt (Nat.le_of_lt_succ S.1.isLt)⟩,
    fun t => S.2 ⟨t.val, Nat.lt_of_le_of_lt (Nat.le_of_lt_succ t.isLt) k.isLt⟩⟩

end TightClock


