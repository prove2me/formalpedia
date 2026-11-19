-- Prove2me | Definitions.Def_DeletionCode_PartialWords
-- name    : DeletionCode_PartialWords
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T04:59:53.631039+00:00
-- url     : https://prove2.me/theorems/30110f13-1d73-4c71-8f1b-a0c3a515a692
-- title:
--   Partial Words
-- statement:
--   Definitions and structural lemmas for Partial Words, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PartialWords.lean

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
set_option autoImplicit true
namespace DeletionCode.PartialWords
open Windows
abbrev Memory := ℕ → Option Bool
abbrev Bits (len : ℕ) := Fin len → Bool
def empty : Memory := fun _ => none
def Sound (s : Memory) (p : Letters) (m : ℕ) : Prop :=
  ∀ j, j < m → ∀ b, s j = some b → b = p j
def Extends (s t : Memory) : Prop :=
  ∀ j b, s j = some b → t j = some b
def Matches {len : ℕ} (bits : Bits len) (p : Letters) (start : ℕ) : Prop :=
  ∀ i, bits i = p (start + i.val)
def readBits (s : Memory) (start len : ℕ) : Option (Bits len) :=
  if ∀ i : Fin len, s (start + i.val) = some ((s (start + i.val)).getD false)
  then some (fun i => (s (start + i.val)).getD false)
  else none
def Compatible (s : Memory) (start : ℕ) {len : ℕ} (bits : Bits len) : Prop :=
  ∀ i, s (start + i.val) = none ∨ s (start + i.val) = some (bits i)
instance (s : Memory) (start : ℕ) {len : ℕ} (bits : Bits len) :
    Decidable (Compatible s start bits) := by
  unfold Compatible
  infer_instance
def putBits (s : Memory) (start : ℕ) {len : ℕ} (bits : Bits len) : Memory :=
  fun j => if h : start ≤ j ∧ j < start + len
    then some (bits ⟨j - start, by omega⟩)
    else s j
def writeBits (s : Memory) (m start : ℕ) {len : ℕ} (bits : Bits len) : Option Memory :=
  if start + len ≤ m ∧ Compatible s start bits
  then some (putBits s start bits)
  else none
end DeletionCode.PartialWords


