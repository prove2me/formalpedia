-- Prove2me | Definitions.Def_BitDFT_HeaderOffsets
-- name    : BitDFT_HeaderOffsets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T15:54:21.411851+00:00
-- url     : https://prove2.me/theorems/12b48090-6215-4a1f-bbb8-7e284a957eed
-- title:
--   Header-reader configurations at arbitrary input offsets
-- statement:
--   Prepared and final full configurations for the stopped binary header reader, allowing an arbitrary preceding input prefix. The final configuration retains the parsed binary field and clears the unary length counter.
-- source:
--   Extends the existing stopped header-reader interface to later fields of a single native input.

import Definitions.Def_BitDFT_HeaderStage

namespace BitDFT.HeaderOffsets
open IntMul

/-- Prepared before the reader's start transition: the input head is just before the field. -/
def rawPrepared (x : List Bool) (offset : ℕ) : HeaderReader.machine.Cfg where
  state := .start
  cells := fun i => if i = 0 then
      HeaderReader.machine.tapeOf (x.map HeaderReader.machine.bitSym ++ [TapeCopy.Sym.sep])
    else HeaderReader.machine.tapeOf []
  head := fun i => if i = 0 then offset else 0

def prepared (x : List Bool) (offset : ℕ) : HeaderReader.stage.machine.Cfg :=
  MachineSequence.stopCfg HeaderReader.machine HeaderReader.State.copy (by decide) (rawPrepared x offset)

/-- The exact handoff layout: the input suffix is next, the field is retained, and the counter is empty. -/
def rawFinished (x : List Bool) (offset : ℕ) (v : List Bool) : HeaderReader.machine.Cfg where
  state := .copy
  cells := fun i => if i = 0 then
      HeaderReader.machine.tapeOf (x.map HeaderReader.machine.bitSym ++ [TapeCopy.Sym.sep])
    else if i = 1 then HeaderReader.machine.tapeOf []
    else if i = 2 then HeaderReader.machine.tapeOf []
    else HeaderReader.machine.tapeOf (v.map HeaderReader.machine.bitSym)
  head := fun i => if i = 0 then offset+2*v.length+2 else if i = 1 then 1
    else if i = 2 then 0 else v.length+1

def finished (x : List Bool) (offset : ℕ) (v : List Bool) : HeaderReader.stage.machine.Cfg :=
  MachineSequence.stopCfg HeaderReader.machine HeaderReader.State.copy (by decide) (rawFinished x offset v)

end BitDFT.HeaderOffsets


