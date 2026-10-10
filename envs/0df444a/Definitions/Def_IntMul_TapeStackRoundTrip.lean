-- Prove2me | Definitions.Def_IntMul_TapeStackRoundTrip
-- name    : IntMul_TapeStackRoundTrip
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T21:44:48.629505+00:00
-- url     : https://prove2.me/theorems/fa4407b4-1844-42be-9770-ea12b119f12c
-- title:
--   Literal seventeen-state stack round-trip caller with charged push-to-pop dispatch
-- statement:
--   Defines one fixed four-tape, five-symbol, seventeen-state caller using a finite Bool continuation. It starts the stack push, takes one actual preserving transition from push halt to pop entry, runs pop and takes one actual transition to global halt. The table never receives a stack depth, ancestor length, head address or full configuration. Initial and final frames describe arbitrary saved prefixes and prepared local word/scratch suffixes. No input-dependent tapes or states are introduced.
-- source:
--   Original actual one-way MultitapeTM formalization of the fixed-control stack push/pop strategy in CrocSwap/integer-mult-bounds research/machine-transfer-verification/transfer-proof/tapes/TapeStack*.lean, pinned at 3b6b66891c0ac888521cf591fe306c6286601d4f. Written by Codex.

import Definitions.Def_IntMul_TapeStack
import Definitions.Def_IntMul_FiniteCaller

namespace IntMul.TapeStackRoundTrip

open IntMul.TapeCopy (Sym)

/-- One finite bit chooses between returning from push to pop and global
halt after pop. Each choice is one actual transition preserving all heads. -/
def dispatch (popping : Bool) (_ : Fin 4 → Sym) : Option (Bool × TapeStack.State) :=
  if popping then none else some (true,.popDelimiter)

/-- A fixed four-tape, five-symbol, seventeen-state physical round-trip
caller. No stack depth is encoded in finite control. -/
noncomputable abbrev machine : MultitapeTM :=
  FiniteCaller.machine TapeStack.machine Bool false dispatch

def initialFrame (base : TapeStack.machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) : machine.Cfg :=
  FiniteCaller.embed TapeStack.machine Bool false false dispatch (TapeStack.pushFrame base sigma rho tau w 0)

def finalFrame (base : TapeStack.machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) : machine.Cfg where
  state := none
  cells := (TapeStack.popDoneFrame base sigma rho tau w).cells
  head := (TapeStack.popDoneFrame base sigma rho tau w).head

end IntMul.TapeStackRoundTrip


