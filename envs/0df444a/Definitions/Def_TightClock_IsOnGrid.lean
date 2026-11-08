-- Prove2me | Definitions.Def_TightClock_IsOnGrid
-- name    : TightClock_IsOnGrid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:42:37.93711+00:00
-- url     : https://prove2.me/theorems/e9eed4ad-7d75-417a-930b-60d9f4347d1c
-- title:
--   Prior supported on a public grid
-- statement:
--   A finite prior is **on a public grid** if there is $\delta>0$ with every support point in $\delta\mathbb Z_{\ge 0}$. This is the grid of §3, $v_i\in\delta\mathbb Z_{\ge0}$, which Theorem 6.1 asks of its prior.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.13 (PDF p.16); Theorem 6.1, p.34 (PDF p.37)

import Mathlib
import Definitions.Def_TightClock_FinitePrior

set_option autoImplicit false

namespace TightClock

/-- The prior is supported on a public grid: all support points lie in `δ ℤ≥0` for some `δ > 0`.
Afshinmehr et al., manuscript (STOC 2027 submission), §3, p.13 (PDF 16) and Theorem 6.1, p.34 (PDF 37). -/
def IsOnGrid (D : FinitePrior) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ D.support, ∃ m : ℕ, x = δ * (m : ℝ)

end TightClock


