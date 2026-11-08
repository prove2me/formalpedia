-- Prove2me | Definitions.Def_TightClock_Path
-- name    : TightClock_Path
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:52:12.572055+00:00
-- url     : https://prove2.me/theorems/2c56e95a-dde9-461a-89d0-bb26fd9b4126
-- title:
--   Tree nodes at depth $r$, as index paths
-- statement:
--   A node at depth $r$ of the hierarchical tree is an index path: for each level $s<r$, the choice of one of the $K_{s+1}$ children. There are $\bar K_r$ such paths.
--
--   **Formalization Note** A node is its path and not its set of bidders. This is what the paper asks: "Different nodes may contain the same set of bidders, but we still treat them as different nodes".
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Instance 11, §6.2, p.35 (PDF p.38)

import Mathlib
import Definitions.Def_TightClock_K

set_option autoImplicit false

namespace TightClock

/-- The nodes at depth `r` of the hierarchical tree, as index paths: at each level `s < r` a choice of one
of the `K_{s+1}` children. Afshinmehr et al., manuscript (STOC 2027 submission), Instance 11, §6.2, p.35
(PDF 38): "Different nodes may contain the same set of bidders, but we still treat them as different nodes."

**Formalization Note** A node is its index path, not its set of bidders. -/
abbrev Path (q L r : ℕ) : Type := (s : Fin r) → Fin (K q L (s.val + 1))

end TightClock


