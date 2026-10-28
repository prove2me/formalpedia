-- Prove2me | Definitions.Def_BitDFT_ParsedPrecision
-- name    : BitDFT_ParsedPrecision
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T16:04:54.42259+00:00
-- url     : https://prove2.me/theorems/3a9bba04-d34d-4a7b-b98a-81d2defff35b
-- title:
--   A fixed machine preparing and computing precision from parsed headers
-- statement:
--   A fixed five-tape machine sequences the header setup controller and guard-precision program. Initially the requested precision word is on tape 3 and the canonical dimension word is on tape 4, with heads just past their ends and tape 2 empty. Setup reverses the precision word and places the heads before invoking the precision program.
-- source:
--   Actual finite-controller composition of HeaderSetup and PrecisionProgram; native request parsing and output serialization are separate stages.

import Definitions.Def_BitDFT_HeaderSetup
import Definitions.Def_BitDFT_PrecisionProgram

namespace BitDFT.ParsedPrecision
open IntMul MachineSequence

/-- The preparation controller and precision controller use the same five physical tapes. -/
def setupControl : Controller PrecisionProgram.machine where
  K := HeaderSetup.machine.K
  entry := HeaderSetup.machine.qStart
  exit := HeaderSetup.machine.qHalt
  distinct := HeaderSetup.machine.start_ne_halt
  transition := HeaderSetup.machine.δ
  marker := HeaderSetup.machine.start_preserved
  noMarker := HeaderSetup.machine.start_only_at_start
  frozen := HeaderSetup.machine.halt_fixed
  readonly := HeaderSetup.machine.input_readonly

noncomputable abbrev machine := sequence setupControl (native PrecisionProgram.machine) |>.machine

def setupBase (base : PrecisionProgram.arithmetic.Cfg) : HeaderSetup.machine.Cfg where
  state := .start
  cells := base.cells
  head := base.head

def setupInitial (base : PrecisionProgram.arithmetic.Cfg) (tail w : List Bool) : setupControl.machine.Cfg where
  state := .start
  cells := (HeaderSetup.frame (setupBase base) .start w [] (true::tail) 0 (w.length+1) (tail.length+2)).cells
  head := (HeaderSetup.frame (setupBase base) .start w [] (true::tail) 0 (w.length+1) (tail.length+2)).head

noncomputable def initial (base : PrecisionProgram.arithmetic.Cfg) (tail w : List Bool) : machine.Cfg :=
  leftCfg setupControl (native PrecisionProgram.machine) (setupInitial base tail w)

noncomputable def final (base : PrecisionProgram.arithmetic.Cfg) (tail v : List Bool) : machine.Cfg :=
  rightCfg setupControl (native PrecisionProgram.machine) (PrecisionProgram.final base tail v)

end BitDFT.ParsedPrecision


