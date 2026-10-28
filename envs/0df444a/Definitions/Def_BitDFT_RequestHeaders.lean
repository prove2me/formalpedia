-- Prove2me | Definitions.Def_BitDFT_RequestHeaders
-- name    : BitDFT_RequestHeaders
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T16:09:26.81558+00:00
-- url     : https://prove2.me/theorems/98070471-bcfd-4c84-9881-18a102ca3a4b
-- title:
--   A fixed five-tape machine reading both request headers
-- statement:
--   The machine parses two consecutive self-delimiting binary headers from native input. It retains the first field on tape 4, resets the native input/output heads by one transition, and parses the second field on tape 3 while preserving the first. The input suffix remains on the read-only native tape.
-- source:
--   Composition of the stopped header reader, a tape extension, a tape permutation, and an explicit one-step reset controller.

import Definitions.Def_BitDFT_HeaderOffsets
import Definitions.Def_BitDFT_TapeExtension
import Definitions.Def_BitDFT_TapePermutation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases

noncomputable section
namespace BitDFT.RequestHeaders
open IntMul MachineSequence
abbrev reader := HeaderReader.stage.machine
abbrev second := TapeExtension.machine reader 1

def swap34 : Fin 5 ≃ Fin 5 := Equiv.swap 3 4
abbrev first := TapePermutation.machine second swap34 (by decide)

def firstControl : Controller second where
  K := first.K
  entry := first.qStart
  exit := first.qHalt
  distinct := first.start_ne_halt
  transition := first.δ
  marker := first.start_preserved
  noMarker := first.start_only_at_start
  frozen := first.halt_fixed
  readonly := first.input_readonly

/-- A single transition backs up the input/output heads before the next reader start. -/
def resetTransition (q : Bool) (a : Fin 5 → second.Sym) : Bool × (Fin 5 → second.Sym × Move) :=
  (true,fun i => HeaderReader.protect (a i) (a i, if q then .stay else if i = 0 ∨ i = 1 then .left else .stay))

def reset : Controller second where
  K := Bool
  entry := false
  exit := true
  distinct := by decide
  transition := resetTransition
  marker := by
    intro q a i hi
    simp only [resetTransition,HeaderReader.protect,hi,if_true]
    split <;> split <;> simp_all
  noMarker := by
    intro q a i hi
    simp [resetTransition,HeaderReader.protect,hi]
  frozen := by
    intro a
    apply Prod.ext
    · rfl
    · funext i
      by_cases h : a i = TapeCopy.Sym.start <;> simp [resetTransition,HeaderReader.protect,h]
  readonly := by
    intro q a
    by_cases h : a 0 = TapeCopy.Sym.start <;> simp [resetTransition,HeaderReader.protect,h,MultitapeTM.inTape]

noncomputable abbrev restControl := sequence reset (native second)
noncomputable abbrev machine := (sequence firstControl restControl).machine

def header (v : List Bool) := List.replicate v.length true ++ false::v

def firstInitial (x : List Bool) : firstControl.machine.Cfg :=
  TapePermutation.embed second swap34 (by decide)
    (TapeExtension.embed reader 1 (fun _ => second.tapeOf []) (fun _ => 0)
      (HeaderOffsets.prepared x 0))

def firstFinished (x n : List Bool) : firstControl.machine.Cfg :=
  TapePermutation.embed second swap34 (by decide)
    (TapeExtension.embed reader 1 (fun _ => second.tapeOf []) (fun _ => 0)
      (HeaderOffsets.finished x 0 n))

def secondInitial (x n : List Bool) : second.Cfg :=
  TapeExtension.embed reader 1 (fun _ => second.tapeOf (n.map second.bitSym)) (fun _ => n.length+1)
    (HeaderOffsets.prepared x (header n).length)

def secondFinished (x n b : List Bool) : second.Cfg :=
  TapeExtension.embed reader 1 (fun _ => second.tapeOf (n.map second.bitSym)) (fun _ => n.length+1)
    (HeaderOffsets.finished x (header n).length b)

noncomputable def final (x n b : List Bool) : machine.Cfg :=
  rightCfg firstControl restControl (rightCfg reset (native second) (secondFinished x n b))

end BitDFT.RequestHeaders


