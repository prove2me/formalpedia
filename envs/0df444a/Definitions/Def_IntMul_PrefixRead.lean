-- Prove2me | Definitions.Def_IntMul_PrefixRead
-- name    : IntMul_PrefixRead
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T13:14:26.437253+00:00
-- url     : https://prove2.me/theorems/fa5671fd-3ba8-4234-bb31-38c3adbd383e
-- title:
--   Prepared counted prefix-read frame on an ordinary binary tape
-- statement:
--   The existing fixed four-tape counted-stream machine reads a prefix from a plain finite binary input tape at an interior cursor. Two physically prepared counter/template banks retain the binary word for the desired prefix length minus one. The output may already contain a retained prefix. The input tape contains no appended descriptor; real counter decrement and template restoration control the length. Full frames record every cell and head. Correctness and the linear clock are separate theorem obligations; incoming counter and cursor preparation remains explicit.
-- source:
--   Prepared ordinary-binary prefix reader for real output width conversion. Reuses the exact counted-stream finite machine and does not add a transition table. Written by Codex.

import Definitions.Def_IntMul_CountedStreamFrames

namespace IntMul.PrefixRead

open TapeCopy (Sym)
abbrev machine := CountedStream.machine

/-- Complete live frame for a block at an interior read-only input cursor.
The descriptor templates and output prefix have already been physically prepared.
The retained read bank contains only the ordinary binary payload, with no appended descriptor.
They are preserved or extended by actual transitions, with no free cursor change. -/
def frame (pre x tail a z bits : List Bool) (j : ℕ) (q : CountedStream.State) : machine.Cfg where
  state := q
  cells := fun i =>
    if i=0 then machine.tapeOf ((pre++x++tail).map machine.bitSym)
    else if i=1 then machine.tapeOf ((a++x.take j).map machine.bitSym)
    else if i=2 then machine.tapeOf (Sym.sep::(bits.reverse.map machine.bitSym++[Sym.sep]))
    else machine.tapeOf (Sym.sep::(z.map machine.bitSym++[Sym.sep]))
  head := fun i => if i=0 then pre.length+j+1 else if i=1 then a.length+j+1
    else z.length+1

def ready (pre x tail a z : List Bool) (j : ℕ) (q : CountedStream.State) : machine.Cfg :=
  frame pre x tail a z z.reverse j q

end IntMul.PrefixRead


