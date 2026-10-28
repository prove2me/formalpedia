-- Prove2me | Definitions.Def_BitDFT_PrecisionProgram
-- name    : BitDFT_PrecisionProgram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T15:27:30.14828+00:00
-- url     : https://prove2.me/theorems/9ef61ff8-2c4f-474f-b4cc-abaaf7ce4782
-- title:
--   A single five-tape program that constructs and adds the guard-precision increment
-- statement:
--   A fixed five-tape program combines the proved logarithmic scanner and binary counter. Native input/output remain on tapes 0/1. The reversed requested-precision bits are parked on tape 2, the unary workspace is tape 3, and the canonical dimension word is on tape 4. A finite tape permutation routes the scanner to tape 4 while it constructs the count on tape 3. A one-transition controller handoff then invokes the counter on tapes 2/3. The final configuration retains the dimension word and caller data, holds the computed precision bits on tape 2, and clears tape 3. Parsing and installing these initial words, and serializing the result, are separate stages.
-- source:
--   Explicit composition of the existing BitDFT logarithmic scanner, unary-controlled binary counter, tape-extension and tape-permutation adapters, and sequential finite-controller construction.

import Definitions.Def_BitDFT_LogScanner
import Definitions.Def_BitDFT_BinaryCounter
import Definitions.Def_BitDFT_TapeExtension
import Definitions.Def_BitDFT_TapePermutation
import Definitions.Def_BitDFT_MachineSequence
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases

namespace BitDFT.PrecisionProgram
open IntMul

abbrev scanExtended := TapeExtension.machine LogScanner.machine 1
abbrev arithmetic := TapeExtension.machine BinaryCounter.machine 1

def swap24 : Fin 5 ≃ Fin 5 := Equiv.swap 2 4

abbrev scanRouted := TapePermutation.machine scanExtended swap24 (by decide)

/-- The scanner uses tape 4 for n, keeping the binary precision on tape 2 parked. -/
def scanControl : MachineSequence.Controller arithmetic where
  K := scanRouted.K
  entry := scanRouted.qStart
  exit := scanRouted.qHalt
  distinct := scanRouted.start_ne_halt
  transition := scanRouted.δ
  marker := scanRouted.start_preserved
  noMarker := scanRouted.start_only_at_start
  frozen := scanRouted.halt_fixed
  readonly := scanRouted.input_readonly

/-- A single fixed five-tape machine: prepare the unary logarithmic increment, then add it. -/
noncomputable abbrev machine :=
  (MachineSequence.sequence scanControl (MachineSequence.native arithmetic)).machine

def base4 (base : arithmetic.Cfg) : LogScanner.machine.Cfg where
  state := .start
  cells := fun i => base.cells (TapeExtension.oldTape LogScanner.machine 1 i)
  head := fun i => base.head (TapeExtension.oldTape LogScanner.machine 1 i)

def scanInitial (base : arithmetic.Cfg) (tail w : List Bool) : scanControl.machine.Cfg :=
  TapePermutation.embed scanExtended swap24 (by decide)
    (TapeExtension.embed LogScanner.machine 1
      (fun _ => BinaryCounter.machine.tapeOf (w.reverse.map BinaryCounter.machine.bitSym))
      (fun _ => 1)
      (LogScanner.frame (base4 base) .start (true::tail) 1 0 1))

noncomputable def initial (base : arithmetic.Cfg) (tail w : List Bool) : machine.Cfg :=
  MachineSequence.leftCfg scanControl (MachineSequence.native arithmetic) (scanInitial base tail w)

def finalArithmetic (base : arithmetic.Cfg) (tail v : List Bool) : arithmetic.Cfg where
  state := .halt
  cells := fun i => if i = 2 then arithmetic.tapeOf (v.map arithmetic.bitSym)
    else if i = 3 then arithmetic.tapeOf []
    else if i = 4 then arithmetic.tapeOf ((true::tail).map arithmetic.bitSym)
    else base.cells i
  head := fun i => if i = 2 then 1 else if i = 3 then 0
    else if i = 4 then tail.length+2 else base.head i

noncomputable def final (base : arithmetic.Cfg) (tail v : List Bool) : machine.Cfg :=
  MachineSequence.rightCfg scanControl (MachineSequence.native arithmetic) (finalArithmetic base tail v)


def scanFinished (base : arithmetic.Cfg) (tail w : List Bool) : scanControl.machine.Cfg :=
  let k := 3*IntMul.lg (IntMul.val (true::tail))+5
  TapePermutation.embed scanExtended swap24 (by decide)
    (TapeExtension.embed LogScanner.machine 1
      (fun _ => BinaryCounter.machine.tapeOf (w.reverse.map BinaryCounter.machine.bitSym))
      (fun _ => 1)
      (LogScanner.frame (base4 base) .halt (true::tail) (tail.length+2) k k))

def counterBase4 (base : arithmetic.Cfg) : BinaryCounter.machine.Cfg where
  state := .tick
  cells := fun i => base.cells (TapeExtension.oldTape BinaryCounter.machine 1 i)
  head := fun i => base.head (TapeExtension.oldTape BinaryCounter.machine 1 i)

def counterInitial (base : arithmetic.Cfg) (tail w : List Bool) : arithmetic.Cfg :=
  let k := 3*IntMul.lg (IntMul.val (true::tail))+5
  TapeExtension.embed BinaryCounter.machine 1
    (fun _ => arithmetic.tapeOf ((true::tail).map arithmetic.bitSym))
    (fun _ => tail.length+2)
    (BinaryCounter.frame (counterBase4 base) .tick w.reverse k 1)

end BitDFT.PrecisionProgram


