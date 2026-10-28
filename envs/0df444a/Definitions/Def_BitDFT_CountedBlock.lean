-- Prove2me | Definitions.Def_BitDFT_CountedBlock
-- name    : BitDFT_CountedBlock
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T17:50:49.837722+00:00
-- url     : https://prove2.me/theorems/ac6f0e3a-5d40-4877-b3e5-0bc9b3b95054
-- title:
--   A live counted payload block with independent input and output prefixes
-- statement:
--   A complete configuration of the proved counted-stream machine places the input head after an arbitrary prefix, the output head after an independent existing output word, and a binary descriptor in both countdown and saved-template tapes. Each emission appends the next payload bit. The input has an ordinary blank tail; no scan to an input terminator or descriptor-loading setup is built into this frame.
-- source:
--   Adapted from IntMul.CountedStream for coordinate extraction in the exact Fourier output scaler. The descriptor must be physically prepared before this live block is invoked.

import Definitions.Def_IntMul_CountedStream

namespace BitDFT.CountedBlock
open IntMul IntMul.CountedStream
open IntMul.TapeCopy (Sym)

/-- A live counted block with independent input/output prefixes. The descriptor
    is already present in the countdown and saved-template tapes. -/
def frame (pre out x y bits : List Bool) (j : ℕ) (q : State) : machine.Cfg where
  state := q
  cells := fun i => if i = 0 then machine.tapeOf ((pre++x).map machine.bitSym)
    else if i = 1 then machine.tapeOf ((out++x.take j).map machine.bitSym)
    else if i = 2 then machine.tapeOf (Sym.sep :: (bits.reverse.map machine.bitSym++[Sym.sep]))
    else machine.tapeOf (Sym.sep :: (y.map machine.bitSym++[Sym.sep]))
  head := fun i => if i = 0 then pre.length+j+1 else if i = 1 then out.length+j+1 else y.length+1

end BitDFT.CountedBlock


