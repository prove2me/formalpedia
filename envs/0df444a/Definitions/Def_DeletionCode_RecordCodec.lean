-- Prove2me | Definitions.Def_DeletionCode_RecordCodec
-- name    : DeletionCode_RecordCodec
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:09:45.726199+00:00
-- url     : https://prove2.me/theorems/c4b21bdc-e82f-496c-aa4c-8ab9194c1823
-- title:
--   Record Codec
-- statement:
--   Definitions and structural lemmas for Record Codec, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordCodec.lean

import Definitions.Def_DeletionCode_ConcreteDecoder
import Definitions.Def_DeletionCode_DescriptionCount
import Mathlib.Tactic.FinCases
set_option autoImplicit true
namespace DeletionCode.RecordCodec
open HeaderRecovery ConcreteDecoder DescriptionCount
def InstructionBounded (L : ℕ) {B : Type*} : Instruction B → Prop
  | .start _ _ sourceOffset _ _ destOffset _ =>
      sourceOffset ≤ 2 * L ∧ destOffset ≤ 2 * L
  | .fillBase _ _ seedOffset => seedOffset ≤ 2 * L
  | .fillSupplier _ _ sourceOffset _ _ => sourceOffset ≤ 2 * L
instance (L : ℕ) {B : Type*} (instruction : Instruction B) :
    Decidable (InstructionBounded L instruction) := by
  cases instruction <;> unfold InstructionBounded <;> infer_instance
def bitCode (bit : Bool) : ℕ := if bit then 1 else 0
def orientationCode (orientation : Orientation) : ℕ :=
  match orientation with
  | .deletion => 0
  | .insertion => 1
theorem bitCode_le (bit : Bool) : bitCode bit ≤ 1 := by cases bit <;> decide
theorem orientationCode_le (orientation : Orientation) : orientationCode orientation ≤ 1 := by
  cases orientation <;> decide
def encodeHeader (L : ℕ) (header : Header)
    (hrho0 : 1 ≤ header.rho) (hrhoL : header.rho ≤ L) : Fin (4 * L) :=
  ⟨4 * (header.rho - 1) + 2 * orientationCode header.orientation + bitCode header.bit, by
    have ho := orientationCode_le header.orientation
    have hb := bitCode_le header.bit
    omega⟩
def decodeHeader {L : ℕ} (code : Fin (4 * L)) : Header where
  rho := code.val / 4 + 1
  orientation := if code.val % 4 < 2 then .deletion else .insertion
  bit := code.val % 2 == 1
abbrev Row (L ν : ℕ) := Fin 12 → Fin (fieldBound L ν)
def instructionField {ν : ℕ} (instruction : Instruction (Fin ν)) (i : Fin 12) : ℕ :=
  match instruction with
  | .start source sourceSide sourceOffset dest destSide destOffset extra =>
    match i.val with
    | 0 => 1
    | 1 => source.val
    | 2 => bitCode sourceSide
    | 3 => sourceOffset
    | 4 => dest.val
    | 5 => bitCode destSide
    | 6 => destOffset
    | 7 => bitCode extra
    | _ => 0
  | .fillBase dest window seedOffset =>
    match i.val with
    | 0 => 2
    | 1 => dest.val
    | 2 => window.val
    | 3 => seedOffset
    | _ => 0
  | .fillSupplier source sourceSide sourceOffset dest window =>
    match i.val with
    | 0 => 3
    | 1 => source.val
    | 2 => bitCode sourceSide
    | 3 => sourceOffset
    | 4 => dest.val
    | 5 => window.val
    | _ => 0
theorem instructionField_lt (L ν : ℕ) (hL : 1 ≤ L) (hν : 1 ≤ ν)
    (instruction : Instruction (Fin ν)) (hbound : InstructionBounded L instruction)
    (i : Fin 12) : instructionField instruction i < fieldBound L ν := by
  have hlargeOffset : 2 * L < fieldBound L ν := by unfold fieldBound; nlinarith
  have hlargeName : ν < fieldBound L ν := by unfold fieldBound; nlinarith
  have hlargeTag : 4 < fieldBound L ν := by unfold fieldBound; nlinarith
  cases instruction with
  | start source sourceSide sourceOffset dest destSide destOffset extra =>
    have hsource := source.isLt
    have hdest := dest.isLt
    have hsourceSide := bitCode_le sourceSide
    have hdestSide := bitCode_le destSide
    have hextra := bitCode_le extra
    rcases hbound with ⟨hs, hd⟩
    fin_cases i <;> simp only [instructionField] <;> omega
  | fillBase dest window seedOffset =>
    have hdest := dest.isLt
    have hwindow := window.isLt
    change seedOffset ≤ 2 * L at hbound
    fin_cases i <;> simp only [instructionField] <;> omega
  | fillSupplier source sourceSide sourceOffset dest window =>
    have hsource := source.isLt
    have hdest := dest.isLt
    have hwindow := window.isLt
    have hsourceSide := bitCode_le sourceSide
    change sourceOffset ≤ 2 * L at hbound
    fin_cases i <;> simp only [instructionField] <;> omega
def encodeInstruction (L ν : ℕ) (hL : 1 ≤ L) (hν : 1 ≤ ν)
    (instruction : Instruction (Fin ν)) (hbound : InstructionBounded L instruction) : Row L ν :=
  fun i => ⟨instructionField instruction i, instructionField_lt L ν hL hν instruction hbound i⟩
def nameFromNat (ν : ℕ) (hν : 1 ≤ ν) (value : ℕ) : Fin ν :=
  ⟨value % ν, Nat.mod_lt value (by omega)⟩
def slotFromNat (value : ℕ) : Recovery.Slot := ⟨value % 3, Nat.mod_lt value (by omega)⟩
def bitFromNat (value : ℕ) : Bool := value % 2 == 1
def decodeInstruction (L ν : ℕ) (hν : 1 ≤ ν) (row : Row L ν) :
    Option (Option (Instruction (Fin ν))) :=
  match (row 0).val with
  | 0 => some none
  | 1 => some (some (.start
      (nameFromNat ν hν (row 1).val) (bitFromNat (row 2).val) (row 3).val
      (nameFromNat ν hν (row 4).val) (bitFromNat (row 5).val) (row 6).val
      (bitFromNat (row 7).val)))
  | 2 => some (some (.fillBase
      (nameFromNat ν hν (row 1).val) (slotFromNat (row 2).val) (row 3).val))
  | 3 => some (some (.fillSupplier
      (nameFromNat ν hν (row 1).val) (bitFromNat (row 2).val) (row 3).val
      (nameFromNat ν hν (row 4).val) (slotFromNat (row 5).val)))
  | _ => none
def zeroRow (L ν : ℕ) (hL : 1 ≤ L) (_hν : 1 ≤ ν) : Row L ν :=
  fun _ => ⟨0, by unfold fieldBound; nlinarith⟩
end DeletionCode.RecordCodec


