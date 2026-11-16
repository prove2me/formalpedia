-- Prove2me | Definitions.Def_TightClock_Supplement_ProgStep
-- name    : TightClock_Supplement_ProgStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:01:38.316255+00:00
-- url     : https://prove2.me/theorems/a3091e38-52b9-4e22-95ab-7f56742fb4bb
-- title:
--   One small step of a clock program
-- statement:
--   The result of executing a clock program for one step: either the program has **finished** with a value, or its next visible action is an **offer** of a price $p$ to a bidder $i$ together with the continuation on her answer, or it made an **internal step** to another program without making an offer. This is the vocabulary of the operational semantics that turns clock programs into clock auctions.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.13 (PDF p.16)

import Mathlib
import Definitions.Def_TightClock_Supplement_ClockProg

set_option autoImplicit false

namespace TightClock.Supplement

/-- The result of one small step of a clock program: it has finished with a value (`done`), its next
visible action is an offer with a continuation on the answer (`ask`), or it made an internal step
without any offer (`tau`). Used to give `ClockProg` its meaning as a clock. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §3, p.13
(PDF 16). -/
inductive ProgStep (n : ℕ) (α : Type) : Type 1
  /-- The program returned `a`. -/
  | done (a : α)
  /-- The program offers `p` to `i` and continues with `k` on her answer. -/
  | ask (i : Fin n) (p : ℝ) (k : Bool → ClockProg n α)
  /-- An internal step to `next`, with no offer. -/
  | tau (next : ClockProg n α)

end TightClock.Supplement


