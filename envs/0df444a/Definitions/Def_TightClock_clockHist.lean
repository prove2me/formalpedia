-- Prove2me | Definitions.Def_TightClock_clockHist
-- name    : TightClock_clockHist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:53:09.795845+00:00
-- url     : https://prove2.me/theorems/6c8f9142-3aef-448c-b8bb-bfdb720476b9
-- title:
--   Run of a clock on a value profile
-- statement:
--   Fix a deterministic clock $\sigma$ and a profile $v$. The run starts with the empty history. If $\sigma$ offers $p$ to $i$ at the current history, then the record $(i,p,\mathbb 1[v_i\ge p])$ is appended: bidder $i$ accepts exactly when $v_i\ge p$. If $\sigma$ stops, the history stays as it is.
--
--   **Formalization Note** The run is a sequence indexed by all of $\mathbb N$, since nothing bounds the number of rounds and a clock need not stop.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.13 (PDF p.16)

import Mathlib
import Definitions.Def_TightClock_Strategy

set_option autoImplicit false

namespace TightClock

/-- The history of the clock `σ` on the profile `v` after `t` steps. A bidder accepts exactly when
`v i ≥ p`. After a `stop` the history no longer changes. Afshinmehr et al., manuscript (STOC 2027
submission), §3, p.13 (PDF 16): "Bidder i accepts exactly when vi ≥ p." -/
noncomputable def clockHist {n : ℕ} (σ : Strategy n) (v : Fin n → ℝ) : ℕ → History n
  | 0 => []
  | t + 1 =>
    match σ (clockHist σ v t) with
    | .offer i p => clockHist σ v t ++ [⟨i, p, decide (p ≤ v i)⟩]
    | .stop _ => clockHist σ v t

end TightClock


