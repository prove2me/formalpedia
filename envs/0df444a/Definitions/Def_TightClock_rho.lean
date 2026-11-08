-- Prove2me | Definitions.Def_TightClock_rho
-- name    : TightClock_rho
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:43:42.860394+00:00
-- url     : https://prove2.me/theorems/929b82b3-5444-448e-bbeb-f538caa17cfe
-- title:
--   Heads probability $\rho=a/M$, (6.1)
-- statement:
--   The coin bias $\rho:=a/M$ of (6.1), equal to $1/(Lq^5)$. Thus $M\rho=a$, display (6.3), "the heart of the construction".
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.35 (PDF p.38), eq. (6.1)

import Mathlib
import Definitions.Def_TightClock_a
import Definitions.Def_TightClock_M

set_option autoImplicit false

namespace TightClock

/-- The heads probability `ρ := a/M` of (6.1). Afshinmehr et al., manuscript (STOC 2027 submission), §6.2,
p.35 (PDF 38). -/
noncomputable def rho (q L : ℕ) : ℝ := a q / (M q L : ℝ)

end TightClock


