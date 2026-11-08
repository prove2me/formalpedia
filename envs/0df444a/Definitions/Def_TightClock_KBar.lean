-- Prove2me | Definitions.Def_TightClock_KBar
-- name    : TightClock_KBar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:51:17.002941+00:00
-- url     : https://prove2.me/theorems/0e8ee99b-00e7-43ea-bf14-c7333918e4b2
-- title:
--   Number of nodes $\bar K_r=K_1\cdots K_r$
-- statement:
--   There are $\bar K_r:=K_1K_2\cdots K_r$ nodes at depth $r$. The maximal feasible sets are among the leaves, so the instance has at most $\bar K_L$ maximal feasible sets.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.36 (PDF p.39)

import Mathlib
import Definitions.Def_TightClock_K

set_option autoImplicit false

namespace TightClock

/-- The number of nodes at depth `r`, `K̄_r := K₁ K₂ ⋯ K_r`. Afshinmehr et al., manuscript (STOC 2027
submission), §6.2, p.36 (PDF 39). -/
def KBar (q L r : ℕ) : ℕ := ∏ s ∈ Finset.range r, K q L (s + 1)

end TightClock


