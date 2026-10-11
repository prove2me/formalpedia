-- Prove2me | Definitions.Def_IntMul_WordWidthCounter
-- name    : IntMul_WordWidthCounter
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T15:07:56.438903+00:00
-- url     : https://prove2.me/theorems/af27dec4-dc18-4dca-9af5-057db912c74c
-- title:
--   Actual framed bit-word length counter with retained source and empty output
-- statement:
--   The accepted physical input counter is used from an explicit marked source bit word, without the original operand separator. Initially the word occupies source tape 0, output and counter banks are empty, and all heads are at their real start markers. The exact terminal frame retains the word and empty output, while the growing little-endian counter on work bank 2 represents max(word length,1)-1. Empty and singleton words are included. Correctness, counter value, exact logarithmic representation width and actual linear transition bound are separate theorem obligations.
-- source:
--   Physical framed-word specialization enabling an already computed descriptor to be counted without a supplied length. Written by Codex.

import Definitions.Def_IntMul_InputWidthCounter

namespace IntMul.WordWidthCounter
open TapeCopy (Sym)
noncomputable abbrev machine : MultitapeTM := InputWidthCounter.machine

def counterWord (w : List Bool) : List Bool := GrowingCounter.iterateCounter (w.length-1) []
/-- Explicit actual marked source bit word, empty output and counter banks,
all heads initially at their real markers. No word length is supplied to delta. -/
noncomputable def initialFrame (w : List Bool) : machine.Cfg where
  state := machine.qStart
  cells := fun i => if i=0 then machine.tapeOf (w.map machine.bitSym) else machine.tapeOf []
  head := fun _ => 0
/-- The source is retained; the counter represents max(|w|,1)-1, including
empty and singleton words. Output remains empty at its marker. -/
noncomputable def finalFrame (w : List Bool) : machine.Cfg where
  state := none
  cells := fun i => if i=0 then machine.tapeOf (w.map machine.bitSym)
    else if i=2 then machine.tapeOf ((counterWord w).map machine.bitSym) else machine.tapeOf []
  head := fun i => if i=0 then w.length+1 else if i=2 then 1 else 0
end IntMul.WordWidthCounter


