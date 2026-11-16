-- Prove2me | Definitions.Def_TightClock_Supplement_betaM
-- name    : TightClock_Supplement_betaM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:14:58.904192+00:00
-- url     : https://prove2.me/theorems/4294bd48-de2d-4461-a01d-5e1c0a3581c2
-- title:
--   $\beta_m$, (5.1)
-- statement:
--   For $m=\lceil\log(8d)\rceil$, $\beta_m>1$ is the unique solution of
--
--   $$\beta_m\log\beta_m-\beta_m+1=\log(4m).$$
--
--   It is the approximation parameter of Theorem 5.1, and $\beta_m=\Theta(\log\log d/\log\log\log d)$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §5, (5.1), p.21 (PDF p.24)

import Mathlib
import Definitions.Def_TightClock_Supplement_betaRoot
import Definitions.Def_TightClock_Supplement_headSize

set_option autoImplicit false

namespace TightClock.Supplement

/-- `β_m > 1`, the unique solution of `β_m log β_m − β_m + 1 = log(4m)` for `m = ⌈log(8d)⌉`,
display (5.1). Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §5, p.21 (PDF 24). -/
noncomputable def betaM {n : ℕ} (F : Finset (Finset (Fin n))) : ℝ :=
  betaRoot (Real.log (4 * (headSize F : ℝ)))

end TightClock.Supplement


