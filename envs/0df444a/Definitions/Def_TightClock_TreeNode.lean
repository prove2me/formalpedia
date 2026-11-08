-- Prove2me | Definitions.Def_TightClock_TreeNode
-- name    : TightClock_TreeNode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:00:24.893785+00:00
-- url     : https://prove2.me/theorems/7c33c816-3f09-4f11-a3e3-f71ee82bea6a
-- title:
--   Node of the tree, at any depth
-- statement:
--   A node of the tree, at any depth $0\le r\le L$: its depth and its index path.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Instance 11, §6.2, p.35 (PDF p.38)

import Mathlib
import Definitions.Def_TightClock_Path

set_option autoImplicit false

namespace TightClock

/-- A node of the tree, at some depth `r ≤ L`. Afshinmehr et al., manuscript (STOC 2027 submission),
Instance 11, §6.2, p.35 (PDF 38). -/
abbrev TreeNode (q L : ℕ) : Type := Σ r : Fin (L + 1), Path q L r.val

end TightClock


