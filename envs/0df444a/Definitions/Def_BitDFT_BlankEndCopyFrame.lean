-- Prove2me | Definitions.Def_BitDFT_BlankEndCopyFrame
-- name    : BitDFT_BlankEndCopyFrame
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T08:54:08.953985+00:00
-- url     : https://prove2.me/theorems/2fa1ebe9-3653-4d19-93c9-7abb9d0c4abd
-- title:
--   Frame for copying a bit suffix terminated by blank
-- statement:
--   The blank-ended copier frame stores an arbitrary bit string directly on its source tape, with no explicit separator, and stores a prefix on its destination tape. It records the source and destination head positions and can be used with the existing copier, whose transition halts whenever the scanned source symbol is not a bit.
-- source:
--   This frame adapts the accepted two-tape suffix copier to the blank-terminated magnitude scratch tape produced by coordinate extraction.

import Definitions.Def_BitDFT_SuffixCopyTwoTape

namespace BitDFT.SuffixCopyTwoTape
open IntMul

/-- A suffix copier frame whose source ends in blank rather than an explicit
    separator. The copier stops on any non-bit symbol. -/
def blankEndFrame (base : machine.Cfg) (q : State)
    (input out : List Bool) (ip : ℕ) : machine.Cfg where
  state := q
  cells := fun i => if i = 0 then machine.tapeOf (input.map machine.bitSym)
    else machine.tapeOf (out.map machine.bitSym)
  head := fun i => if i = 0 then ip else out.length+1

end BitDFT.SuffixCopyTwoTape


