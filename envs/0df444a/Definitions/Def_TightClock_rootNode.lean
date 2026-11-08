-- Prove2me | Definitions.Def_TightClock_rootNode
-- name    : TightClock_rootNode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:05:33.646209+00:00
-- url     : https://prove2.me/theorems/73a3213b-36a6-41fb-a442-36dcad7c2d4c
-- title:
--   Root node
-- statement:
--   The root of the tree, the unique node at depth $0$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Instance 11, §6.2, p.35 (PDF p.38)

import Mathlib
import Definitions.Def_TightClock_TreeNode

set_option autoImplicit false

namespace TightClock

/-- The root, at depth `0`. Afshinmehr et al., manuscript (STOC 2027 submission), Instance 11, §6.2, p.35
(PDF 38). -/
def rootNode (q L : ℕ) : TreeNode q L := ⟨⟨0, Nat.succ_pos L⟩, fun t => t.elim0⟩

end TightClock


