-- Prove2me | Definitions.Def_TightClock_ssWelfare
-- name    : TightClock_ssWelfare
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:10:51.130329+00:00
-- url     : https://prove2.me/theorems/80b77118-4582-466e-9891-697eba513fc1
-- title:
--   Welfare of a single-step clock run
-- statement:
--   The welfare of a single-step clock on $v$ is the total value of the set it serves.
--
--   **Formalization Note** The served set is unique, since the history no longer changes after the first stop. A valid single-step clock always stops within $nL$ steps, so the fallback value $0$ for a run without a stop is unused for those.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.14 (PDF p.17); §6.2, p.35 (PDF p.38)

import Mathlib
import Definitions.Def_TightClock_ssHist

set_option autoImplicit false

namespace TightClock

open Classical in
/-- The welfare of a single-step clock on the profile `v`: the sum of values of the served set, and `0` if the run
does not stop. Afshinmehr et al., manuscript (STOC 2027 submission), §3, p.14 (PDF 17); §6.2, p.35 (PDF 38).

**Formalization Note** A valid single-step clock always stops within `nL` steps, so the `0` branch is unused for
those. -/
noncomputable def ssWelfare (q L : ℕ) (σ : SingleStepStrategy (bidderCount q L))
    (v : Fin (bidderCount q L) → ℝ) : ℝ :=
  if h : ∃ S t, σ (ssHist q L σ v t) = .stop S then ∑ i ∈ h.choose, v i else 0

end TightClock


