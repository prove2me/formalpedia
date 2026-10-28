-- Prove2me | Definitions.Def_BitDFT_PrepareCall
-- name    : BitDFT_PrepareCall
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T17:17:56.831249+00:00
-- url     : https://prove2.me/theorems/e359836d-8894-4b1d-ab90-f19bfdf1c6fa
-- title:
--   Native preprocessing followed by physical child-input buffer preparation
-- statement:
--   Sequence the routed request preprocessor with the caller-compatible buffer shifter. The resulting fixed machine uses 5+r tapes and an arbitrary caller alphabet. It starts from ordinary native input, rewrites the Fourier precision header, and places the resulting word after a blank gap with a trailing separator. The definition includes exact handoff and final configurations.
-- source:
--   Actual native-input preparation stage for the arbitrary Fourier-machine call in the finite-precision DFT transfer.

import Definitions.Def_BitDFT_PreprocessorPlacement
import Definitions.Def_BitDFT_BufferShiftOn

noncomputable section
namespace BitDFT.PrepareCall
open IntMul MachineSequence

abbrev preprocess (N : MultitapeTM) (r : ℕ) := PreprocessorPlacement.machine N r
abbrev shiftControl (N : MultitapeTM) (r : ℕ) := BufferShiftOn.control (preprocess N r)
abbrev machine (N : MultitapeTM) (r : ℕ) :=
  (sequence (native (preprocess N r)) (shiftControl N r)).machine

def smallBase (c : RewriteInput.machine.Cfg) : BufferShift.machine.Cfg where
  state := .start
  cells := fun i => c.cells ⟨i.val,by have hi : i.val < 2 := i.isLt; change i.val < 5; omega⟩
  head := fun i => c.head ⟨i.val,by have hi : i.val < 2 := i.isLt; change i.val < 5; omega⟩

def shiftBase (N : MultitapeTM) (r : ℕ) (c : RewriteInput.machine.Cfg) :
    (shiftControl N r).machine.Cfg :=
  handoff (native (preprocess N r)) (shiftControl N r) (PreprocessorPlacement.embed N r c)

def shiftStart (N : MultitapeTM) (r : ℕ) (c : RewriteInput.machine.Cfg) (w : List Bool) :
    (shiftControl N r).machine.Cfg :=
  BufferShiftOn.embed (preprocess N r) (shiftBase N r c)
    (AlphabetEmbedding.embed (BufferShiftOn.alphabetMap (preprocess N r))
      (BufferShift.frame (smallBase c) .start (w.map BufferShift.machine.bitSym) (w.length+1)))

def shiftFinish (N : MultitapeTM) (r : ℕ) (c : RewriteInput.machine.Cfg) (w : List Bool) :
    (shiftControl N r).machine.Cfg :=
  BufferShiftOn.embed (preprocess N r) (shiftBase N r c)
    (AlphabetEmbedding.embed (BufferShiftOn.alphabetMap (preprocess N r))
      (BufferShift.frame (smallBase c) .halt ([.blank]++w.map BufferShift.machine.bitSym++[.sep]) 1))

def final (N : MultitapeTM) (r : ℕ) (c : RewriteInput.machine.Cfg) (w : List Bool) :
    (machine N r).Cfg :=
  rightCfg (native (preprocess N r)) (shiftControl N r) (shiftFinish N r c w)

end BitDFT.PrepareCall


