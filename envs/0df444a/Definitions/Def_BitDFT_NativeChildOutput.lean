-- Prove2me | Definitions.Def_BitDFT_NativeChildOutput
-- name    : BitDFT_NativeChildOutput
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T17:35:17.798167+00:00
-- url     : https://prove2.me/theorems/549abe23-cba1-4418-b598-c225012d4eb0
-- title:
--   Native request-to-child-output wrapper with physical output placement
-- statement:
--   Append a caller-compatible version of the proved returned-buffer shift to the arbitrary child-call program. The resulting fixed finite machine uses 5+M.k tapes, starts from ordinary requested input, and ends with the child’s binary output in native output cells one onward. Its full final configuration retains the three preprocessor workspace tapes.
-- source:
--   Native output completion for the arbitrary Fourier-child call used in the integer multiplication to finite-precision DFT transfer.

import Definitions.Def_BitDFT_ChildCall
import Definitions.Def_IntMul_TrackedOutputShift

noncomputable section
namespace BitDFT.NativeChildOutput
open IntMul

abbrev child (M : MultitapeTM) := TrackedOutputShift.machine M
abbrev preparation (M : MultitapeTM) := ChildCall.program M

def oldTape (M : MultitapeTM) (i : Fin (child M).k) : Fin (preparation M).k :=
  ⟨i.val,by have hi : i.val < M.k+2 := i.isLt; change i.val < 5+M.k; omega⟩

def transition (M : MultitapeTM) (q : (child M).K)
    (a : Fin (preparation M).k → (preparation M).Sym) :
    (child M).K × (Fin (preparation M).k → (preparation M).Sym × Move) :=
  let result := (child M).δ q (fun i => a (oldTape M i))
  (result.1,fun i => if h : i.val < (child M).k then result.2 ⟨i.val,h⟩ else (a i,.stay))

def control (M : MultitapeTM) : MachineSequence.Controller (preparation M) where
  K := (child M).K
  entry := (child M).qStart
  exit := (child M).qHalt
  distinct := (child M).start_ne_halt
  transition := transition M
  marker := by
    intro q a i hi
    dsimp only [transition]
    split
    · rename_i h
      exact (child M).start_preserved q (fun j => a (oldTape M j)) ⟨i.val,h⟩ hi
    · simp [hi]
  noMarker := by
    intro q a i hi
    dsimp only [transition]
    split
    · rename_i h
      exact (child M).start_only_at_start q (fun j => a (oldTape M j)) ⟨i.val,h⟩ hi
    · exact hi
  frozen := by
    intro a
    have h := (child M).halt_fixed (fun i => a (oldTape M i))
    change (((child M).δ (child M).qHalt (fun i => a (oldTape M i))).1,
      fun i => if hi : i.val < (child M).k then
        ((child M).δ (child M).qHalt (fun j => a (oldTape M j))).2 ⟨i.val,hi⟩ else (a i,.stay)) = _
    rw [h]
    congr 1
    funext i
    split <;> rfl
  readonly := by
    intro q a
    have hk : 0 < (child M).k := by have := (child M).two_le_k; omega
    simp only [transition,MultitapeTM.inTape,hk,dite_true]
    exact (child M).input_readonly q (fun j => a (oldTape M j))

abbrev machine (M : MultitapeTM) := (control M).machine

def embed (M : MultitapeTM) (base : (preparation M).Cfg) (c : (child M).Cfg) : (machine M).Cfg where
  state := c.state
  cells := fun i => if h : i.val < (child M).k then c.cells ⟨i.val,h⟩ else base.cells i
  head := fun i => if h : i.val < (child M).k then c.head ⟨i.val,h⟩ else base.head i

def project (M : MultitapeTM) (base : (preparation M).Cfg) : (child M).Cfg where
  state := (child M).qStart
  cells := fun i => base.cells (oldTape M i)
  head := fun i => base.head (oldTape M i)



abbrev program (M : MultitapeTM) :=
  (MachineSequence.sequence (MachineSequence.native (preparation M)) (control M)).machine

def final (M : MultitapeTM) (base : (preparation M).Cfg) (w : List Bool) : (program M).Cfg :=
  MachineSequence.rightCfg (MachineSequence.native (preparation M)) (control M)
    (embed M base (TrackedOutputShift.finalFrame M (project M base) w))

end BitDFT.NativeChildOutput


