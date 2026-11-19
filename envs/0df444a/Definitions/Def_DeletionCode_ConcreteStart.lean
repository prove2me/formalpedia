-- Prove2me | Definitions.Def_DeletionCode_ConcreteStart
-- name    : DeletionCode_ConcreteStart
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:07:19.380001+00:00
-- url     : https://prove2.me/theorems/1e4107c5-9810-48d0-ace4-e0a1730cbab1
-- title:
--   Concrete Start
-- statement:
--   Definitions and structural lemmas for Concrete Start, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteStart.lean

import Definitions.Def_DeletionCode_HeaderRecovery
import Definitions.Def_DeletionCode_SelectedWindows
set_option autoImplicit true
namespace DeletionCode.ConcreteStart
open Windows PartialWords SelectedWindows
open HeaderRecovery (Header negativePath positivePath negativeLength positiveLength
  transferFinite windowLength editOffset negativeExtra)
def startNegative (k : ℕ) (h : Header) (offset : ℕ) (bits : PartialWords.Bits k)
    (s : Memory) : Option Memory :=
  writeBits s (negativeLength k h) offset bits
def startPositive (k : ℕ) (h : Header) (offset : ℕ) (bits : PartialWords.Bits k)
    (extra : Bool) (s : Memory) : Option Memory :=
  if offset + k ≤ positiveLength k h then
    let transferred := transferFinite k h offset bits extra
    writeBits s (negativeLength k h) transferred.1 transferred.2
  else none
def StartedCorrectly (k : ℕ) (h : Header) (long : Letters) (s t : Memory) : Prop :=
  Sound t (negativePath k h long) (negativeLength k h) ∧ Extends s t ∧
    ∃ w : Recovery.Slot,
      SeedKnown t (windowStart (negativeExtra k h) w) (windowLength k) k
end DeletionCode.ConcreteStart


