-- Prove2me | Definitions.Def_IntMul_FramedBlockRead
-- name    : IntMul_FramedBlockRead
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T10:34:48.534516+00:00
-- url     : https://prove2.me/theorems/4dfa9fe7-2325-46c0-b627-abd2978d62ff
-- title:
--   Complete live interior block-reader frames
-- statement:
--   The actual counted-stream machine is reused without changing its finite table. Its complete live frames describe an interior read-only input cursor following a retained prefix, a writable output cursor following an arbitrary retained output prefix, a current binary countdown and its saved descriptor. All four physical tapes have their actual start markers and all heads are explicit. These are incoming caller frames, not the global initialization. Correctness and clock bounds are separate obligations.
-- source:
--   Original complete interior coefficient-reader frames in the integer multiplication multitape model. Written by Codex.

import Definitions.Def_IntMul_CountedStreamFrames

namespace IntMul.FramedBlockRead

open TapeCopy (Sym)
abbrev machine := CountedStream.machine

/-- Complete live frame for a block at an interior read-only input cursor.
The descriptor templates and output prefix have already been physically prepared.
They are preserved or extended by actual transitions, with no free cursor change. -/
def frame (pre x tail a z bits : List Bool) (j : ℕ) (q : CountedStream.State) : machine.Cfg where
  state := q
  cells := fun i =>
    if i=0 then machine.tapeOf ((pre++x++tail).map machine.bitSym++Sym.sep::z.map machine.bitSym)
    else if i=1 then machine.tapeOf ((a++x.take j).map machine.bitSym)
    else if i=2 then machine.tapeOf (Sym.sep::(bits.reverse.map machine.bitSym++[Sym.sep]))
    else machine.tapeOf (Sym.sep::(z.map machine.bitSym++[Sym.sep]))
  head := fun i => if i=0 then pre.length+j+1 else if i=1 then a.length+j+1
    else z.length+1

def ready (pre x tail a z : List Bool) (j : ℕ) (q : CountedStream.State) : machine.Cfg :=
  frame pre x tail a z z.reverse j q

end IntMul.FramedBlockRead


