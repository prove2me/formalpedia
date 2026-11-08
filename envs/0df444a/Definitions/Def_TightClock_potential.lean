-- Prove2me | Definitions.Def_TightClock_potential
-- name    : TightClock_potential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:32:52.730904+00:00
-- url     : https://prove2.me/theorems/830c4dc8-cd87-4ded-9eaa-e9184c9d7cb7
-- title:
--   Potential $\Phi(J)$
-- statement:
--   The potential at a state $J$ is
--
--   $$\Phi(J):=\log A(J)+\frac{3\,\mathrm{act}(J)}{n}.$$
--
--   Each active bidder carries a reserve of $3/n$, which pays for the auction's shifts of attention to newly exceptional nodes.
--
--   **Formalization Note** $A(J)$ contains the root's account, which is positive, so the logarithm is genuine.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.6, p.45 (PDF p.48)

import Mathlib
import Definitions.Def_TightClock_trackedMass
import Definitions.Def_TightClock_activeCount

set_option autoImplicit false

namespace TightClock

/-- The potential `Φ(J) := log A(J) + 3 act(J) / n`. Afshinmehr et al., manuscript (STOC 2027 submission), §6.6,
p.45 (PDF 48).

**Formalization Note** `A(J)` is a positive sum, since it contains the root's account, so the logarithm is
genuine. -/
noncomputable def potential {q L : ℕ} (T : Tree q L) (J : State q L) : ℝ :=
  Real.log (trackedMass T J) + 3 * (activeCount J : ℝ) / (bidderCount q L : ℝ)

end TightClock


