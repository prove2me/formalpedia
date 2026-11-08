-- Prove2me | Definitions.Def_TightClock_leafNode
-- name    : TightClock_leafNode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:04:28.352128+00:00
-- url     : https://prove2.me/theorems/ba9e899f-075a-4a58-ad73-31858722b2b6
-- title:
--   Leaf node
-- statement:
--   A leaf of the tree: a node at depth $L$, given by its index path.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Instance 11, §6.2, p.35 (PDF p.38)

import Mathlib
import Definitions.Def_TightClock_TreeNode

set_option autoImplicit false

namespace TightClock

/-- The leaf with index path `s`, at depth `L`. Afshinmehr et al., manuscript (STOC 2027 submission),
Instance 11, §6.2, p.35 (PDF 38). -/
def leafNode {q L : ℕ} (s : Path q L L) : TreeNode q L := ⟨Fin.last L, s⟩

end TightClock


