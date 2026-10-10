-- Prove2me | Definitions.Def_IntMul_CountedStreamFrames
-- name    : IntMul_CountedStreamFrames
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T19:38:41.59732+00:00
-- url     : https://prove2.me/theorems/c0945d7a-099c-4b45-947d-c36045e2b2fb
-- title:
--   Initialized counted-stream block boundary configurations
-- statement:
--   Defines the complete initialized/reusable boundary configuration for the literal counted-stream table. Input x#y is unchanged, output contains x.take j, both work tapes contain the original delimited descriptor y, input/output heads point to item j+1, and both work heads are at the descriptor least significant position. The frame is proof data; the finite transition table does not inspect it.
-- source:
--   The campaign MultitapeTM conventions and exact machine model, published definition 47ff1689-4e87-4af2-9406-674787e32429. Original finite-table compiler and interface formalization, Written by Codex.

import Definitions.Def_IntMul_CountedStream

namespace IntMul.CountedStream

open IntMul.TapeCopy (Sym)

/-- An initialized block boundary: the emitted prefix occupies tape 1, both
local descriptor tapes hold the saved original word, and the heads are ready
for the next input bit and for a least-significant-first decrement. -/
def readyFrame (x y : List Bool) (j : ℕ) (q : State) : machine.Cfg where
  state := q
  cells := fun i =>
    if i = 0 then machine.tapeOf (x.map machine.bitSym ++ Sym.sep :: y.map machine.bitSym)
    else if i = 1 then machine.tapeOf ((x.take j).map machine.bitSym)
    else machine.tapeOf (Sym.sep :: (y.map machine.bitSym ++ [Sym.sep]))
  head := fun i => if i = 0 ∨ i = 1 then j + 1 else y.length + 1

end IntMul.CountedStream


