-- Prove2me | Definitions.Def_BitDFT_LowOperandCopy
-- name    : BitDFT_LowOperandCopy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T23:53:08.957231+00:00
-- url     : https://prove2.me/theorems/b88717af-d77d-46c5-81b6-5dbe334be2d7
-- title:
--   Signed-word low-operand extraction machine
-- statement:
--   A composed tape machine skips the sign and highest magnitude bit of a signed binary word, then copies the remaining low-order bits onto a clean multiplier operand tape. The original word is preserved, and a unary counter provides the exact skip distance.
-- source:
--   A finite-tape adapter for constructing scaled multiplier operands in the integer multiplication to DFT reduction.

import Definitions.Def_BitDFT_UnaryAdvance
import Definitions.Def_BitDFT_TapeExtension
import Definitions.Def_BitDFT_SuffixCopyTwoTape
import Definitions.Def_BitDFT_MachineSequence

noncomputable section
namespace BitDFT.LowOperandCopy
open IntMul MachineSequence

abbrev storage := TapeExtension.machine SuffixCopyTwoTape.machine 1
abbrev sourceTape : Fin storage.k := ⟨0, by simp [storage]⟩
abbrev counterTape : Fin storage.k := ⟨2, by simp [storage]⟩

def advance (h : sourceTape ≠ counterTape) : Controller storage :=
  UnaryAdvance.control storage sourceTape counterTape h

abbrev copy : Controller storage := MachineSequence.native storage
abbrev machine (h : sourceTape ≠ counterTape) := (sequence (advance h) copy).machine

def initialBase (sign high : Bool) (bits : List Bool) : storage.Cfg :=
  { state := storage.qStart
    cells := fun i =>
      if i.val = 0 then storage.tapeOf ((([sign, high] ++ bits).map storage.bitSym) ++ [storage.sep])
      else if i.val = 2 then storage.tapeOf [storage.one, storage.one]
      else storage.tapeOf []
    head := fun _ => 1 }

def initial (h : sourceTape ≠ counterTape) (sign high : Bool) (bits : List Bool) :
    (machine h).Cfg :=
  leftCfg (advance h) copy
    (UnaryAdvance.frame storage sourceTape counterTape h
      (initialBase sign high bits) false 1 1)

def copyStartBase (sign high : Bool) (bits : List Bool) : storage.Cfg :=
  { state := storage.qStart
    cells := fun i =>
      if i.val = 0 then storage.tapeOf ((([sign, high] ++ bits).map storage.bitSym) ++ [storage.sep])
      else if i.val = 2 then storage.tapeOf [storage.one, storage.one]
      else storage.tapeOf []
    head := fun i => if i.val = 0 then 3 else if i.val = 2 then 3 else 1 }

def finalBase (sign high : Bool) (bits : List Bool) : storage.Cfg :=
  { state := storage.qHalt
    cells := fun i =>
      if i.val = 0 then storage.tapeOf ((([sign, high] ++ bits).map storage.bitSym) ++ [storage.sep])
      else if i.val = 1 then storage.tapeOf (bits.map storage.bitSym)
      else storage.tapeOf [storage.one, storage.one]
    head := fun i => if i.val = 0 then 2 + (bits.length + 1) else if i.val = 1 then bits.length + 1 else 3 }

def final (h : sourceTape ≠ counterTape) (sign high : Bool) (bits : List Bool) :
    (machine h).Cfg :=
  rightCfg (advance h) copy (finalBase sign high bits)

end BitDFT.LowOperandCopy


