-- Prove2me | Definitions.Def_TightClock_parent
-- name    : TightClock_parent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:05:28.616204+00:00
-- url     : https://prove2.me/theorems/ed4e7deb-3b8c-4a02-ba7b-b8f5fe616217
-- title:
--   Parent $\mathrm{par}(S)$ of a node
-- statement:
--   The parent $\mathrm{par}(S)$ of a node at depth $r+1$ is the node at depth $r$ whose index path is the path of $S$ without its last choice.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Definition 6.8, §6.5, p.43 (PDF p.46)

import Mathlib
import Definitions.Def_TightClock_NonrootNode
import Definitions.Def_TightClock_TreeNode

set_option autoImplicit false

namespace TightClock

/-- The parent `par(S)` of a node at depth `r + 1`: its path with the last choice removed. Afshinmehr et
al., manuscript (STOC 2027 submission), Definition 6.8, §6.5, p.43 (PDF 46). -/
def parent {q L : ℕ} (D : NonrootNode q L) : TreeNode q L :=
  ⟨⟨D.1.val, Nat.lt_succ_of_lt D.1.isLt⟩, fun t => D.2 (Fin.castSucc t)⟩

end TightClock


