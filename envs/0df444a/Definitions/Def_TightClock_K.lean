-- Prove2me | Definitions.Def_TightClock_K
-- name    : TightClock_K
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:44:28.33821+00:00
-- url     : https://prove2.me/theorems/e9fc4869-9093-4d08-9256-ff7989298944
-- title:
--   Branching number $K_r=q^{4BM^{r-1}}$
-- statement:
--   Each node at depth $r-1$ has $K_r:=q^{4BM^{r-1}}$ children, for $r=1,\dots,L$.
--
--   **Formalization Note** The definition is used for $r\ge 1$ only, where the natural subtraction $r-1$ is exact.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.35 (PDF p.38)

import Mathlib
import Definitions.Def_TightClock_B
import Definitions.Def_TightClock_M

set_option autoImplicit false

namespace TightClock

/-- The branching number `K_r := q^{4 B M^{r-1}}` at depth `r`, a natural number. Afshinmehr et al.,
manuscript (STOC 2027 submission), §6.2, p.35 (PDF 38).

**Formalization Note** It is used for `r ≥ 1` only, where the natural subtraction `r - 1` is exact. It is a
tower in `L`: keep it symbolic. -/
def K (q L r : ℕ) : ℕ := q ^ (4 * B L * (M q L) ^ (r - 1))

end TightClock


