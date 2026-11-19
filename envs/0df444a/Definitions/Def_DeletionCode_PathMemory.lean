-- Prove2me | Definitions.Def_DeletionCode_PathMemory
-- name    : DeletionCode_PathMemory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:07:34.598305+00:00
-- url     : https://prove2.me/theorems/89e8a26a-7380-45d0-a2ad-ae547617468a
-- title:
--   Path Memory
-- statement:
--   Definitions and structural lemmas for Path Memory, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PathMemory.lean

import Definitions.Def_DeletionCode_HeaderRecovery
import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_SelectedWindows
set_option autoImplicit true
namespace DeletionCode.PathMemory
open Windows HeaderRecovery PartialWords SelectedWindows
def pathLength (k : ℕ) (h : Header) (side : Bool) : ℕ :=
  if side then positiveLength k h else negativeLength k h
def pathLetters (k : ℕ) (h : Header) (long : Letters) (side : Bool) : Letters :=
  if side then positivePath k h long else negativePath k h long
def extractBits {m : ℕ} (bits : PartialWords.Bits m) (start len : ℕ)
    (hbound : start + len ≤ m) : PartialWords.Bits len :=
  fun i => bits ⟨start + i.val, by have := i.isLt; omega⟩
def readPath (k : ℕ) (h : Header) (s : Memory) (side : Bool)
    (start len : ℕ) : Option (PartialWords.Bits len) :=
  match side with
  | false => if start + len ≤ negativeLength k h then readBits s start len else none
  | true =>
    if hbound : start + len ≤ positiveLength k h then
      (readBits s 0 (negativeLength k h)).map fun negative =>
        extractBits (rebuildPositiveFinite k h negative) start len hbound
    else none
end DeletionCode.PathMemory


