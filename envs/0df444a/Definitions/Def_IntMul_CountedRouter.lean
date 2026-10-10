-- Prove2me | Definitions.Def_IntMul_CountedRouter
-- name    : IntMul_CountedRouter
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T19:44:09.03698+00:00
-- url     : https://prove2.me/theorems/362c8c05-fdf0-4e7f-b5ac-92bc9ea456c7
-- title:
--   A literal reusable counted-block router with final cleanup
-- statement:
--   A single fixed four-tape, five-symbol, 27-state machine compiles the accepted counted stream with a finite caller bit. It initializes the descriptor once, resumes emission whenever another input bit remains at a block return, and otherwise runs saved-template cleanup before global halt. A final short block stops at the input delimiter and also receives physical cleanup. The transition table sees only finite caller/subroutine state and scanned symbols; it never reads lengths, numeric descriptors, or head positions. Defines the complete restored boundary frame. Every subroutine continuation is an actual transition; correctness and a whole-run bound are separate theorem obligations.
-- source:
--   The campaign MultitapeTM model; the checked finite caller compiler; the accepted literal counted stream and saved-template reset; counter algorithm adapted from the pinned CrocSwap/integer-mult-bounds source cited in IntMul_CountedStream. Original composition, Written by Codex.

import Definitions.Def_IntMul_CountedStreamFrames
import Definitions.Def_IntMul_FiniteCaller

namespace IntMul.CountedRouter

open IntMul.TapeCopy (Sym)

/-- One finite caller bit distinguishes normal counted blocks from final
cleanup. At each block return, a scanned input bit starts the next block;
otherwise the caller enters saved-template reset. Cleanup returns to global
halt. No length, numeric descriptor, or head position is read by this table. -/
def dispatch (cleanup : Bool) (a : Fin 4 → Sym) :
    Option (Bool × CountedStream.State) :=
  if cleanup then none
  else if a 0 = .zero ∨ a 0 = .one then some (false,.emit)
  else some (true,.resetLeft)

/-- A single fixed four-tape, five-symbol, 27-state machine. It initializes its
descriptor once, runs counted blocks, and resets after the final partial block.
Every continuation is an actual transition of `FiniteCaller.machine`. -/
noncomputable abbrev machine : MultitapeTM :=
  FiniteCaller.machine CountedStream.machine Bool false dispatch

/-- Complete boundary configuration, with the copied prefix on output and the
original descriptor restored on both local working tapes. -/
def frame (x y : List Bool) (j : ℕ) (q : Option (Bool × CountedStream.State)) :
    machine.Cfg where
  state := q
  cells := (CountedStream.readyFrame x y j .halt).cells
  head := (CountedStream.readyFrame x y j .halt).head

end IntMul.CountedRouter


