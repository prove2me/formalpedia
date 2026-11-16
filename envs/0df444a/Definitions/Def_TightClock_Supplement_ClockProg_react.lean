-- Prove2me | Definitions.Def_TightClock_Supplement_ClockProg_react
-- name    : TightClock_Supplement_ClockProg_react
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:03:42.703457+00:00
-- url     : https://prove2.me/theorems/c777690c-540a-4234-bf41-4cc9105edff7
-- title:
--   Visible action of a clock program after a history
-- statement:
--   Given the observed acceptance/rejection history of a run, feed each recorded answer to the continuation of the pending offer and return the visible action that follows. The result is "none" if the history does not fit the program (it continues after the program has finished). This implements the rule that the auction's next move is a function of the seed and of the observed history.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.13 (PDF p.16)

import Mathlib
import Definitions.Def_TightClock_Supplement_ClockProg_settle

set_option autoImplicit false

namespace TightClock.Supplement

/-- The visible step of a clock program after the observed history `h`: each recorded answer
(`e.accepted`) is fed to the continuation of the pending offer. `none` if the history does not fit
the program (it continues after the program finished, or the program diverges without offers).
Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §3, p.13 (PDF 16): prices are "a function of the public random seed and the observed
acceptance/rejection history". -/
noncomputable def ClockProg.react {n : ℕ} {α : Type} : ClockProg n α → History n → Option (ProgStep n α)
  | x, [] => x.settle
  | x, e :: h =>
    match x.settle with
    | some (.ask _ _ k) => ClockProg.react (k e.accepted) h
    | _ => none

end TightClock.Supplement


