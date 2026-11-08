-- Prove2me | Definitions.Def_TightClock_y
-- name    : TightClock_y
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:46:03.873133+00:00
-- url     : https://prove2.me/theorems/a2029746-b698-433d-a7d8-3c3cc40b271d
-- title:
--   Tier value $y_j=M^{-j}$
-- statement:
--   Tier $j$ consists of the bidders with value $y_j:=M^{-j}$, for $j=0,\dots,L$. The values run from $y_0=1$ down to $y_L=M^{-L}$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.35 (PDF p.38)

import Mathlib
import Definitions.Def_TightClock_M

set_option autoImplicit false

namespace TightClock

/-- The value `y_j := M⁻ʲ` of tier `j`. Afshinmehr et al., manuscript (STOC 2027 submission), §6.2, p.35
(PDF 38). -/
noncomputable def y (q L j : ℕ) : ℝ := ((M q L : ℝ)⁻¹) ^ j

end TightClock


