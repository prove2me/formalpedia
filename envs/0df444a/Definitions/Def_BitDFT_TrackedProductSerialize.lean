-- Prove2me | Definitions.Def_BitDFT_TrackedProductSerialize
-- name    : BitDFT_TrackedProductSerialize
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T04:28:22.836991+00:00
-- url     : https://prove2.me/theorems/52b17a21-3207-4cf6-a84e-f1bcf627909e
-- title:
--   Copy a normalized multiplier product into the serializer
-- statement:
--   A finite controller starts from a tagged product returned on the multiplier output tape. It rewinds to the tape marker, copies the product bits into the serializer input tape while clearing the old output, installs a blank terminator, rewinds the output head, and then hands control to the existing counted-field serializer. The controller uses a fixed transition table independent of product length; an alphabet embedding and tape-count adapter let it run in the shared multiplier workspace.
-- source:
--   Shared-host connector needed by BitDFT.rescale_output_machine: bridges the accepted tracked multiplier output-normalization frame to the existing finite serializer.

import Definitions.Def_IntMul_TrackedOutputShift
import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_IntMul_TrackedBankedSimulation
import Definitions.Def_IntMul_TrackedBankCleanup
import Definitions.Def_BitDFT_TapeExtension
import Definitions.Def_BitDFT_AlphabetEmbedding
import Definitions.Def_BitDFT_TapeCountTransport
import Definitions.Def_BitDFT_SerializeField
import Definitions.Def_BitDFT_MachineSequence

namespace BitDFT.TrackedProductSerialize
open IntMul BitDFT.MachineSequence

noncomputable abbrev host (M : MultitapeTM) := TapeExtension.machine (TrackedOutputShift.machine M) 1

inductive State
  | seekSource | seekDestination | copy | rewind | halt
  deriving DecidableEq

instance : Fintype State where
  elems := {.seekSource, .seekDestination, .copy, .rewind, .halt}
  complete := by intro q; cases q <;> simp

noncomputable def source (M : MultitapeTM) : Fin (host M).k := ⟨1, by dsimp [host]; omega⟩
noncomputable def destination (M : MultitapeTM) : Fin (host M).k := ⟨4, by dsimp [host]; have := M.two_le_k; omega⟩

private noncomputable def blankCell (M : MultitapeTM) : (host M).Sym := some (M.blank, false)

private noncomputable def raw (M : MultitapeTM) (q : State)
    (a : Fin (host M).k → (host M).Sym) :
    State × (Fin (host M).k → (host M).Sym × Move) := by
  classical
  exact
  let s := source M
  let d := destination M
  let safe (i : Fin (host M).k) (write : (host M).Sym) (move : Move) :=
    if i.val = 0 then (a i, .stay) else (write, move)
  match q with
  | .seekSource =>
      if a s = none then (.seekDestination, fun i => safe i (a i) .stay)
      else (.seekSource, fun i => safe i (a i) (if i = s then .left else .stay))
  | .seekDestination =>
      if a d = none then (.copy, fun i => safe i (a i) (if i = s ∨ i = d then .right else .stay))
      else (.seekDestination, fun i => safe i (a i) (if i = d then .left else .stay))
  | .copy =>
      if TrackedBankedSimulation.decode M (a s) = M.zero ∨
          TrackedBankedSimulation.decode M (a s) = M.one then
        (.copy, fun i => safe i
          (if i = s then blankCell M else if i = d then a s else a i)
          (if i = s ∨ i = d then .right else .stay))
      else (.rewind, fun i => safe i (if i = d then blankCell M else a i)
        (if i = s then .left else .stay))
  | .rewind =>
      if a s = none then (.halt, fun i => safe i (a i) (if i = s then .right else .stay))
      else (.rewind, fun i => safe i (a i) (if i = s then .left else .stay))
  | .halt => (.halt, fun i => (a i, .stay))

noncomputable def transition (M : MultitapeTM) (q : State)
    (a : Fin (host M).k → (host M).Sym) :
    State × (Fin (host M).k → (host M).Sym × Move) :=
  if q = .halt then (.halt, fun i => (a i, .stay)) else
    let r := raw M q a
    (r.1, fun i => TrackedBankCleanup.protect M (a i) (r.2 i).1 (r.2 i).2)

noncomputable def controller (M : MultitapeTM) : Controller (host M) where
  K := State
  entry := .seekSource
  exit := .halt
  distinct := by decide
  transition := transition M
  marker := by
    classical
    intro q a i hi
    by_cases hq : q = .halt
    · simp [transition, hq, hi]
    · simp only [transition, hq, if_false]
      change (TrackedBankCleanup.protect M (a i) _ _).1 = none ∧
        (TrackedBankCleanup.protect M (a i) _ _).2 ≠ .left
      rw [hi]
      simp only [TrackedBankCleanup.protect]
      split <;> simp_all
  noMarker := by
    classical
    intro q a i hi
    by_cases hq : q = .halt
    · simp [transition, hq, hi]
    · simp only [transition, hq, if_false]
      change (TrackedBankCleanup.protect M (a i) _ _).1 ≠ none
      cases h : a i with
      | none => exact False.elim (hi h)
      | some s =>
          cases hw : ((raw M q a).2 i).1 <;>
            simp [TrackedBankCleanup.protect, hw]
  frozen := by intro a; simp [transition]
  readonly := by
    classical
    intro q a
    by_cases hq : q = .halt
    · simp [transition, hq]
    · dsimp only [transition]
      rw [if_neg hq]
      change (TrackedBankCleanup.protect M (a ((host M).inTape))
        ((raw M q a).2 ((host M).inTape)).1
        ((raw M q a).2 ((host M).inTape)).2).1 = a ((host M).inTape)
      have hraw : (raw M q a).2 (⟨0, by have := (host M).two_le_k; omega⟩ : Fin (host M).k) =
          (a ⟨0, by have := (host M).two_le_k; omega⟩, .stay) := by
          cases q <;> simp [raw, MultitapeTM.inTape] <;>
            split_ifs <;> simp [source, destination]
      let input : Fin (host M).k := ⟨0, by have := (host M).two_le_k; omega⟩
      have hin : (host M).inTape = input := rfl
      rw [hin, hraw]
      cases h : a input <;> simp [TrackedBankCleanup.protect, h]

noncomputable def serializeMap (M : MultitapeTM) :
    AlphabetEmbedding.Map SerializeField.machine (host M) where
  encode := {
    toFun := fun s => match s with
      | .blank => some (M.blank, false)
      | .start => none
      | .zero => some (M.zero, true)
      | .one => some (M.one, true)
      | .sep => some (M.sep, true)
    inj' := by
      classical
      intro a b h
      have hd := M.syms_distinct
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at hd
      cases a <;> cases b <;> simp_all
  }
  blank := rfl
  marker := rfl
  zero := rfl
  one := rfl
  sep := rfl

noncomputable abbrev serializerAlphabet (M : MultitapeTM) :=
  AlphabetEmbedding.machine (serializeMap M)

noncomputable abbrev serializerExtended (M : MultitapeTM) :=
  TapeExtension.machine (serializerAlphabet M) ((host M).k - 5)

theorem serializerTapeCount (M : MultitapeTM) :
    (serializerExtended M).k = (host M).k := by
  dsimp [serializerExtended, TapeExtension.machine, serializerAlphabet, host]
  have hm := M.two_le_k
  omega

noncomputable abbrev serializerMachine (M : MultitapeTM) :=
  TapeCountTransport.machine (serializerExtended M) (host M).k (serializerTapeCount M)

noncomputable def serializerController (M : MultitapeTM) : Controller (host M) where
  K := (serializerMachine M).K
  entry := (serializerMachine M).qStart
  exit := (serializerMachine M).qHalt
  distinct := (serializerMachine M).start_ne_halt
  transition := (serializerMachine M).δ
  marker := (serializerMachine M).start_preserved
  noMarker := (serializerMachine M).start_only_at_start
  frozen := (serializerMachine M).halt_fixed
  readonly := (serializerMachine M).input_readonly

noncomputable abbrev program (M : MultitapeTM) :=
  sequence (controller M) (serializerController M)

end BitDFT.TrackedProductSerialize


