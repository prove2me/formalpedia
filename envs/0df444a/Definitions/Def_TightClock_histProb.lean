-- Prove2me | Definitions.Def_TightClock_histProb
-- name    : TightClock_histProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:10:43.80789+00:00
-- url     : https://prove2.me/theorems/c5149c20-0354-4364-9a48-510d252cdabc
-- title:
--   Probability of a history $H^t$
-- statement:
--   The probability that a single-step clock has history $H^t=h$ after $t=|h|$ steps, under the i.i.d. prior $D$ and with tree and seed fixed.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.36 (PDF p.39)

import Mathlib
import Definitions.Def_TightClock_ssHist
import Definitions.Def_TightClock_priorExpect

set_option autoImplicit false

namespace TightClock

open Classical in
/-- The probability, under the i.i.d. prior `D`, that the first `h.length` steps of a single-step clock produce the
history `h`. Afshinmehr et al., manuscript (STOC 2027 submission), §6.2, p.36 (PDF 39).

**Formalization Note** A run that stops before time `h.length` has a shorter history, so the event says exactly that
`h` is the history after `h.length` tests. -/
noncomputable def histProb (q L : ℕ) (D : FinitePrior) (σ : SingleStepStrategy (bidderCount q L))
    (h : SingleStepHistory (bidderCount q L)) : ℝ :=
  priorExpect D (fun v => if ssHist q L σ v h.length = h then 1 else 0)

end TightClock


