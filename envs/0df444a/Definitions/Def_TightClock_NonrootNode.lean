-- Prove2me | Definitions.Def_TightClock_NonrootNode
-- name    : TightClock_NonrootNode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:00:21.481399+00:00
-- url     : https://prove2.me/theorems/96bac146-35af-4199-8be2-4f908117e448
-- title:
--   Non-root node of the tree
-- statement:
--   The nodes of depths $1,\dots,L$ of the tree. These are the nodes with their own coins, and those whose parent is defined.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Instance 11, §6.2, p.35 (PDF p.38)

import Mathlib
import Definitions.Def_TightClock_Path

set_option autoImplicit false

namespace TightClock

/-- A node at some depth `r + 1 ≥ 1`, `r < L`. Afshinmehr et al., manuscript (STOC 2027 submission),
Instance 11, §6.2, p.35 (PDF 38). -/
abbrev NonrootNode (q L : ℕ) : Type := Σ r : Fin L, Path q L (r.val + 1)

end TightClock


