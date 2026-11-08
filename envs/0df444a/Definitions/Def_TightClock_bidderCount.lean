-- Prove2me | Definitions.Def_TightClock_bidderCount
-- name    : TightClock_bidderCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:38:38.559272+00:00
-- url     : https://prove2.me/theorems/119800f0-4b61-42a4-886d-df0446ce7219
-- title:
--   Number of bidders $n=B\rho^{-L}$, (6.1)
-- statement:
--   The number of bidders of the instance:
--
--   $$n:=B\rho^{-L}=L^3(Lq^5)^L.$$
--
--   **Formalization Note** Since $\rho^{-1}=Lq^5$ is an integer, $n$ is written as this natural number.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.35 (PDF p.38), eq. (6.1); p.44 (PDF p.47)

import Mathlib

set_option autoImplicit false

namespace TightClock

/-- The number of bidders `n := Bρ⁻ᴸ = L³ (L q⁵)ᴸ` of (6.1). Afshinmehr et al., manuscript (STOC 2027
submission), §6.2, p.35 (PDF 38) and p.44 (PDF 47).

**Formalization Note** `ρ⁻¹ = L q⁵` is an integer, so `n` is written as the natural number the page
computes on p.44. The verification file proves `(n : ℝ) = B ρ⁻ᴸ` for `q, L ≥ 1`. -/
def bidderCount (q L : ℕ) : ℕ := L ^ 3 * (L * q ^ 5) ^ L

end TightClock


