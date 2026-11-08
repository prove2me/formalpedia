-- Prove2me | Definitions.Def_TightClock_fee
-- name    : TightClock_fee
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:44:49.905199+00:00
-- url     : https://prove2.me/theorems/d8656dcc-6faa-4b12-95a5-0db06ab7c9b0
-- title:
--   Fee per level $h=a^2B/L$
-- statement:
--   The account of a node charges a **fee** per level of depth, $h:=a^2B/L$. The total fee along a root-to-leaf path is $Lh=a^2B$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.4, p.40 (PDF p.43)

import Mathlib
import Definitions.Def_TightClock_a
import Definitions.Def_TightClock_B

set_option autoImplicit false

namespace TightClock

/-- The fee per level `h := a² B / L`. Afshinmehr et al., manuscript (STOC 2027 submission), §6.4, p.40
(PDF 43). -/
noncomputable def fee (q L : ℕ) : ℝ := (a q) ^ 2 * (B L : ℝ) / (L : ℝ)

end TightClock


