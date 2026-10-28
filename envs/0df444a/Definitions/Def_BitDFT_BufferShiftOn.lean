-- Prove2me | Definitions.Def_BitDFT_BufferShiftOn
-- name    : BitDFT_BufferShiftOn
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T17:15:05.461309+00:00
-- url     : https://prove2.me/theorems/af6e7c76-3277-4c03-a6a9-0a147e561b5b
-- title:
--   A buffer-shift controller over any caller alphabet and tape count
-- statement:
--   For every multitape machine N, lift the fixed two-tape buffer shifter into N’s alphabet and execute it on native tapes 0 and 1. All other tapes and heads stay parked. This produces a finite controller using exactly N’s alphabet and tape count, suitable for sequencing with N.
-- source:
--   The caller-compatible controller for physically placing rewritten Fourier input before the tracked call.

import Definitions.Def_BitDFT_BufferShift
import Definitions.Def_BitDFT_PreprocessorAlphabet
import Definitions.Def_BitDFT_MachineSequence

noncomputable section
namespace BitDFT.BufferShiftOn
open IntMul

def alphabetMap (N : MultitapeTM) : AlphabetEmbedding.Map BufferShift.machine N where
  encode := (PreprocessorAlphabet.alphabetMap N).encode
  blank := rfl
  marker := rfl
  zero := rfl
  one := rfl
  sep := rfl

abbrev small (N : MultitapeTM) := AlphabetEmbedding.machine (alphabetMap N)

def oldTape (N : MultitapeTM) (i : Fin 2) : Fin N.k :=
  ⟨i.val,by have := N.two_le_k; omega⟩

def transition (N : MultitapeTM) (q : (small N).K) (a : Fin N.k → N.Sym) :
    (small N).K × (Fin N.k → N.Sym × Move) :=
  let result := (small N).δ q (fun i => a (oldTape N i))
  (result.1,fun i => if h : i.val < 2 then result.2 ⟨i.val,h⟩ else (a i,.stay))

def control (N : MultitapeTM) : MachineSequence.Controller N where
  K := (small N).K
  entry := (small N).qStart
  exit := (small N).qHalt
  distinct := (small N).start_ne_halt
  transition := transition N
  marker := by
    intro q a i hi
    dsimp only [transition]
    split
    · rename_i h
      exact (small N).start_preserved q (fun j => a (oldTape N j)) ⟨i.val,h⟩ hi
    · simp [hi]
  noMarker := by
    intro q a i hi
    dsimp only [transition]
    split
    · rename_i h
      exact (small N).start_only_at_start q (fun j => a (oldTape N j)) ⟨i.val,h⟩ hi
    · exact hi
  frozen := by
    intro a
    simp only [transition,AlphabetEmbedding.transition,if_pos rfl]
    congr 1
    funext i
    split <;> rfl
  readonly := by
    intro q a
    simp only [transition,MultitapeTM.inTape,show (0:ℕ)<2 by decide,dite_true]
    exact (small N).input_readonly q (fun j => a (oldTape N j))

abbrev machine (N : MultitapeTM) := (control N).machine

def embed (N : MultitapeTM) (base : (machine N).Cfg) (c : (small N).Cfg) : (machine N).Cfg where
  state := c.state
  cells := fun i => if h : i.val < 2 then c.cells ⟨i.val,h⟩ else base.cells i
  head := fun i => if h : i.val < 2 then c.head ⟨i.val,h⟩ else base.head i

end BitDFT.BufferShiftOn


