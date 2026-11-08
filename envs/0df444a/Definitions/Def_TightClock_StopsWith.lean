-- Prove2me | Definitions.Def_TightClock_StopsWith
-- name    : TightClock_StopsWith
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:59:15.444515+00:00
-- url     : https://prove2.me/theorems/7b913615-f578-4268-be5a-5a660f3d4f05
-- title:
--   A run terminates with a winner set
-- statement:
--   The run of a deterministic clock on $v$ **stops with** $S$ if the clock plays `stop S` at some step. This $S$ is the terminal winner set $W_\pi(v)$ of §3. It is unique, because the history no longer changes after the first stop.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.14 (PDF p.17)

import Mathlib
import Definitions.Def_TightClock_clockHist

set_option autoImplicit false

namespace TightClock

/-- The run of `σ` on `v` reaches `stop S`. Afshinmehr et al., manuscript (STOC 2027 submission), §3,
p.13 (PDF 16). At most one `S` qualifies, since the history is frozen from the first `stop` on. -/
def StopsWith {n : ℕ} (σ : Strategy n) (v : Fin n → ℝ) (S : Finset (Fin n)) : Prop :=
  ∃ t : ℕ, σ (clockHist σ v t) = .stop S

end TightClock


