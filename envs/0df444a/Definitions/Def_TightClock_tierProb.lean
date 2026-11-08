-- Prove2me | Definitions.Def_TightClock_tierProb
-- name    : TightClock_tierProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:52:15.416778+00:00
-- url     : https://prove2.me/theorems/217010ae-337a-44e2-8b5b-22a80ac318db
-- title:
--   Tier probabilities, (6.2)
-- statement:
--   Every bidder privately tosses $L$ coins in a row, each showing heads with probability $\rho$. She belongs to tier $j$ when her first $L-j$ coins are heads and her next coin, if any, is a tail. Hence
--
--   $$p_0=\rho^L,\qquad p_j=(1-\rho)\rho^{L-j}\quad(1\le j\le L).$$
--
--   **Formalization Note** The definition is used for $j\le L$, where the natural subtraction $L-j$ is exact.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.35 (PDF p.38), eq. (6.2)

import Mathlib
import Definitions.Def_TightClock_rho

set_option autoImplicit false

namespace TightClock

/-- The tier probabilities (6.2): `p₀ = ρᴸ`, `p_j = (1 − ρ) ρ^{L−j}` for `1 ≤ j ≤ L`. Afshinmehr et al.,
manuscript (STOC 2027 submission), §6.2, p.35 (PDF 38).

**Formalization Note** It is used for `j ≤ L`, where the natural subtraction `L - j` is exact. -/
noncomputable def tierProb (q L j : ℕ) : ℝ :=
  if j = 0 then (rho q L) ^ L else (1 - rho q L) * (rho q L) ^ (L - j)

end TightClock


