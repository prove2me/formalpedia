-- Prove2me | Definitions.Def_TightClock_ssHist
-- name    : TightClock_ssHist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:06:55.648283+00:00
-- url     : https://prove2.me/theorems/e00f53c4-7f7d-45bc-870f-6d0e5d402e86
-- title:
--   Run of a single-step clock
-- statement:
--   The run of a single-step clock on the profile $v$. At a test of bidder $i$ with cutoff $j$, the pair $(i,\mathbb 1[v_i\ge y_{j-1}])$ is appended to the history. At a stop the history stays as it is.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, pp.35–36 (PDF pp.38–39)

import Mathlib
import Definitions.Def_TightClock_SingleStepStrategy
import Definitions.Def_TightClock_stateOf
import Definitions.Def_TightClock_testPrice

set_option autoImplicit false

namespace TightClock

/-- The history of a single-step clock on the profile `v` after `t` steps. The tested bidder accepts exactly
when her value is at least the price `y_{j−1}`. After a `stop` the history no longer changes. Afshinmehr et al.,
manuscript (STOC 2027 submission), §6.2, pp.35–36 (PDF 38–39). -/
noncomputable def ssHist (q L : ℕ) (σ : SingleStepStrategy (bidderCount q L))
    (v : Fin (bidderCount q L) → ℝ) : ℕ → SingleStepHistory (bidderCount q L)
  | 0 => []
  | t + 1 =>
    match σ (ssHist q L σ v t) with
    | .test i =>
        ssHist q L σ v t ++ [(i, decide (testPrice q L (stateOf q L (ssHist q L σ v t)) i ≤ v i))]
    | .stop _ => ssHist q L σ v t

end TightClock


