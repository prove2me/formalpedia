-- Prove2me | Definitions.Def_DeletionCode_ConcreteFill
-- name    : DeletionCode_ConcreteFill
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:07:02.888943+00:00
-- url     : https://prove2.me/theorems/e3304641-9976-4abb-a39c-8476e1a8ceb4
-- title:
--   Concrete Fill
-- statement:
--   Definitions and structural lemmas for Concrete Fill, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteFill.lean

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_SeedLookup
set_option autoImplicit true
namespace DeletionCode.ConcreteFill
open Windows PartialWords
def fillFromBase (x : Letters) (n k L : ℕ) (s : Memory) (m start r : ℕ) :
    Option Memory :=
  (readBits s (start + r) k).bind fun seed =>
    (SeedLookup.recoverWindow x n k L r seed).bind fun bits =>
      writeBits s m start bits
def copyFromMemory (source : Memory) (sourceLength sourceStart len : ℕ)
    (s : Memory) (m start : ℕ) : Option Memory :=
  if sourceStart + len ≤ sourceLength then
    (readBits source sourceStart len).bind fun bits => writeBits s m start bits
  else none
def loadRoot (x : Letters) (n a len : ℕ) (s : Memory) (m : ℕ) : Option Memory :=
  if a + len ≤ n then writeBits s m 0 (fun i : Fin len => x (a + i.val))
  else none
def Recovered (s t : Memory) (p : Letters) (m start len : ℕ) : Prop :=
  Sound t p m ∧ Extends s t ∧
    readBits t start len = some (fun i : Fin len => p (start + i.val))
end DeletionCode.ConcreteFill


