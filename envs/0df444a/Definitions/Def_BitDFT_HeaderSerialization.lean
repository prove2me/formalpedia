-- Prove2me | Definitions.Def_BitDFT_HeaderSerialization
-- name    : BitDFT_HeaderSerialization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T16:31:14.763035+00:00
-- url     : https://prove2.me/theorems/d7b3354e-35f6-423b-8123-ac69d5d47aaa
-- title:
--   A fixed machine serializing dimension and canonical precision headers
-- statement:
--   A five-tape machine sequences field serialization, trimming/reversal of the little-endian precision word, and a tape-routed field serializer. It retains the dimension, clears the old precision tape, and appends both headers to any existing output prefix. Native input remains parked.
-- source:
--   Concrete finite-controller composition of SerializeField and TrimReverse, with tape permutation routing the second serializer to the canonical precision field.

import Definitions.Def_BitDFT_SerializeField
import Definitions.Def_BitDFT_TrimReverse
import Definitions.Def_BitDFT_BinaryCounter
import Definitions.Def_BitDFT_TapePermutation
import Definitions.Def_BitDFT_MachineSequence
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section
namespace BitDFT.HeaderSerialization
open IntMul MachineSequence
abbrev storage := SerializeField.machine

def swap34 : Fin 5 ≃ Fin 5 := Equiv.swap 3 4
abbrev routed := TapePermutation.machine storage swap34 (by decide)

def trimControl : Controller storage where
  K := TrimReverse.machine.K
  entry := TrimReverse.machine.qStart
  exit := TrimReverse.machine.qHalt
  distinct := TrimReverse.machine.start_ne_halt
  transition := TrimReverse.machine.δ
  marker := TrimReverse.machine.start_preserved
  noMarker := TrimReverse.machine.start_only_at_start
  frozen := TrimReverse.machine.halt_fixed
  readonly := TrimReverse.machine.input_readonly

def precisionControl : Controller storage where
  K := routed.K
  entry := routed.qStart
  exit := routed.qHalt
  distinct := routed.start_ne_halt
  transition := routed.δ
  marker := routed.start_preserved
  noMarker := routed.start_only_at_start
  frozen := routed.halt_fixed
  readonly := routed.input_readonly

abbrev restControl := sequence trimControl precisionControl
abbrev machine := (sequence (native storage) restControl).machine

def header (v : List Bool) := List.replicate v.length true ++ false::v

def inputBase (base : storage.Cfg) (w : List Bool) : storage.Cfg where
  state := .start
  cells := fun i => if i = 2 then storage.tapeOf (w.map storage.bitSym)
    else if i = 3 then storage.tapeOf [] else base.cells i
  head := fun i => if i = 2 then 1 else if i = 3 then 0 else base.head i

def firstInitial (base : storage.Cfg) (n w out : List Bool) : storage.Cfg :=
  SerializeField.frame (inputBase base w) .start n out (n.length+1)

def firstFinished (base : storage.Cfg) (n w out : List Bool) : storage.Cfg :=
  SerializeField.frame (inputBase base w) .halt n (out++header n) (n.length+1)

def trimBase (base : storage.Cfg) (n w out : List Bool) : TrimReverse.machine.Cfg where
  state := .start
  cells := (firstFinished base n w out).cells
  head := (firstFinished base n w out).head

def trimmed (base : storage.Cfg) (n w out : List Bool) : trimControl.machine.Cfg :=
  TrimReverse.frame (trimBase base n w out) .halt []
    (bin (BinaryCounter.value w).size (BinaryCounter.value w)) 0

def serializerBase (base : storage.Cfg) (n w out : List Bool) : storage.Cfg where
  state := .start
  cells := fun i => (trimmed base n w out).cells (swap34 i)
  head := fun i => (trimmed base n w out).head (swap34 i)

def precisionInitial (base : storage.Cfg) (n w out : List Bool) : precisionControl.machine.Cfg :=
  let v := bin (BinaryCounter.value w).size (BinaryCounter.value w)
  TapePermutation.embed storage swap34 (by decide)
    (SerializeField.frame (serializerBase base n w out) .start v (out++header n) (v.length+1))

def precisionFinished (base : storage.Cfg) (n w out : List Bool) : precisionControl.machine.Cfg :=
  let v := bin (BinaryCounter.value w).size (BinaryCounter.value w)
  TapePermutation.embed storage swap34 (by decide)
    (SerializeField.frame (serializerBase base n w out) .halt v
      (out++header n++header v) (v.length+1))

def initial (base : storage.Cfg) (n w out : List Bool) : machine.Cfg :=
  leftCfg (native storage) restControl (firstInitial base n w out)

def final (base : storage.Cfg) (n w out : List Bool) : machine.Cfg :=
  rightCfg (native storage) restControl
    (rightCfg trimControl precisionControl (precisionFinished base n w out))

end BitDFT.HeaderSerialization


