-- Prove2me | Definitions.Def_TightClock_trackedMass
-- name    : TightClock_trackedMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:30:38.411906+00:00
-- url     : https://prove2.me/theorems/321ed746-e10e-4e42-a744-61d46591f10c
-- title:
--   Tracked mass $A(J)$
-- statement:
--   The total account of the tracked nodes,
--
--   $$A(J):=\sum_{S\in R(J)}A_S(J).$$
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.6, p.45 (PDF p.48)

import Mathlib
import Definitions.Def_TightClock_tracked
import Definitions.Def_TightClock_account

set_option autoImplicit false

namespace TightClock

/-- The tracked mass `A(J) := ∑_{S ∈ R(J)} A_S(J)`. Afshinmehr et al., manuscript (STOC 2027 submission), §6.6,
p.45 (PDF 48). -/
noncomputable def trackedMass {q L : ℕ} (T : Tree q L) (J : State q L) : ℝ :=
  ∑ S ∈ tracked T J, account T S J

end TightClock


