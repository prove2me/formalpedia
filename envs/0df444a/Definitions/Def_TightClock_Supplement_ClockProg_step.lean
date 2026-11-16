-- Prove2me | Definitions.Def_TightClock_Supplement_ClockProg_step
-- name    : TightClock_Supplement_ClockProg_step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:02:18.434535+00:00
-- url     : https://prove2.me/theorems/8a2c2f5e-80f6-489c-aafa-eafddd915daf
-- title:
--   Small-step semantics of clock programs
-- statement:
--   One small step of a clock program: a returned value is finished; an offer is a visible action whose continuation returns the answer; a loop is unrolled once (run the body; on "continue with state $s'$" loop again from $s'$, on "stop with $b$" return $b$); and a sequential composition steps its first component, reassociating nested compositions. The definition is non-recursive, so every step is a total computation.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.13 (PDF p.16)

import Mathlib
import Definitions.Def_TightClock_Supplement_ProgStep

set_option autoImplicit false

namespace TightClock.Supplement

/-- One small step of a clock program (left-associating `bind`s and unrolling `loop`s once). Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission),
§3, p.13 (PDF 16). -/
def ClockProg.step {n : ℕ} : {α : Type} → ClockProg n α → ProgStep n α
  | _, .pure a => .done a
  | _, .offer i p => .ask i p ClockProg.pure
  | _, .loop body s => .tau (.bind (body s) (fun r => Sum.elim (ClockProg.loop body) ClockProg.pure r))
  | _, .bind (.pure a) f => .tau (f a)
  | _, .bind (.offer i p) f => .ask i p f
  | _, .bind (.bind x g) f => .tau (.bind x (fun a => .bind (g a) f))
  | _, .bind (.loop body s) f =>
      .tau (.bind (.bind (body s) (fun r => Sum.elim (ClockProg.loop body) ClockProg.pure r)) f)

end TightClock.Supplement


