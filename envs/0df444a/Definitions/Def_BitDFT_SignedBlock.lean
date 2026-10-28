-- Prove2me | Definitions.Def_BitDFT_SignedBlock
-- name    : BitDFT_SignedBlock
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T18:46:14.847601+00:00
-- url     : https://prove2.me/theorems/10b1cdc5-575b-4cdc-b4a9-eae3cc825e2b
-- title:
--   A signed-record extractor built from one sign copy and a counted magnitude block
-- statement:
--   This four-tape controller copies the current sign bit to the output, then hands control to the counted-block routine at its live emission state. The counted routine copies the next val(y)+1 payload bits using preinitialized counter and template tapes. The native input contains an arbitrary already-read prefix, followed by the sign and remaining payload; the output may have an independent existing prefix.
-- source:
--   Signed-coordinate extraction for the exact Fourier output scaler. The counted-block routine is reused.

import Definitions.Def_BitDFT_CountedBlock
import Definitions.Def_BitDFT_HeaderReader
import Definitions.Def_BitDFT_MachineSequence

noncomputable section
namespace BitDFT.SignedBlock
open IntMul MachineSequence
abbrev storage := CountedStream.machine

def signTransition (q : Bool) (a : Fin 4 → TapeCopy.Sym) : Bool × (Fin 4 → TapeCopy.Sym × Move) :=
  if q then (true,fun i => (a i,.stay)) else
    (true,fun i => HeaderReader.protect (a i)
      (if i = 1 then a 0 else a i,if i = 0 ∨ i = 1 then .right else .stay))

def signControl : Controller storage where
  K := Bool
  entry := false
  exit := true
  distinct := by decide
  transition := signTransition
  marker := by
    intro q a i hi
    cases q
    · simp only [signTransition,Bool.false_eq_true,if_false,HeaderReader.protect,hi,if_true]
      split <;> simp_all
    · exact ⟨hi,by change Move.stay ≠ Move.left; decide⟩
  noMarker := by
    intro q a i hi
    cases q
    · have hp : ∀ (b : TapeCopy.Sym) (w : TapeCopy.Sym × Move), b ≠ .start →
          (HeaderReader.protect b w).1 ≠ .start := by
        intro b w hb
        simp only [HeaderReader.protect,hb,if_false]
        split <;> simp_all
      exact hp _ _ hi
    · exact hi
  frozen := by intro a; rfl
  readonly := by
    intro q a
    cases q
    · simp [signTransition,HeaderReader.protect,MultitapeTM.inTape]
      split <;> simp_all
    · rfl

def blockControl : Controller storage where
  K := storage.K
  entry := .emit
  exit := .halt
  distinct := by decide
  transition := storage.δ
  marker := storage.start_preserved
  noMarker := storage.start_only_at_start
  frozen := storage.halt_fixed
  readonly := storage.input_readonly

def blockFrame (c : storage.Cfg) : blockControl.machine.Cfg := ⟨c.state,c.cells,c.head⟩

abbrev machine := (sequence signControl blockControl).machine

def signStart (pre out : List Bool) (sign : Bool) (x y : List Bool) : signControl.machine.Cfg :=
  let c := CountedBlock.frame pre out (sign::x) y y.reverse 0 .emit
  ⟨false,c.cells,c.head⟩

def afterSign (pre out : List Bool) (sign : Bool) (x y : List Bool) : blockControl.machine.Cfg :=
  blockFrame (CountedBlock.frame (pre++[sign]) (out++[sign]) x y y.reverse 0 .emit)

def signFinal (pre out : List Bool) (sign : Bool) (x y : List Bool) : signControl.machine.Cfg :=
  let c := afterSign pre out sign x y
  ⟨true,c.cells,c.head⟩

def initial (pre out : List Bool) (sign : Bool) (x y : List Bool) : machine.Cfg :=
  leftCfg signControl blockControl (signStart pre out sign x y)

def final (pre out : List Bool) (sign : Bool) (x y : List Bool) : machine.Cfg :=
  rightCfg signControl blockControl
    (blockFrame (CountedBlock.frame (pre++[sign]) (out++[sign]) x y y.reverse (val y+1) .halt))
end BitDFT.SignedBlock


