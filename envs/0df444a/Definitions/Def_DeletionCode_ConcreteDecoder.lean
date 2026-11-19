-- Prove2me | Definitions.Def_DeletionCode_ConcreteDecoder
-- name    : DeletionCode_ConcreteDecoder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:07:49.853412+00:00
-- url     : https://prove2.me/theorems/65262f00-28f1-45d4-ac0c-d80cb9907439
-- title:
--   Concrete Decoder
-- statement:
--   Definitions and structural lemmas for Concrete Decoder, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteDecoder.lean

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Definitions.Def_DeletionCode_PathMemory
set_option autoImplicit true
namespace DeletionCode.ConcreteDecoder
open Windows PartialWords HeaderRecovery SelectedWindows
abbrev Bank (B : Type*) := B → Memory
inductive Instruction (B : Type*) where
  | start (source : B) (sourceSide : Bool) (sourceOffset : ℕ)
      (dest : B) (destSide : Bool) (destOffset : ℕ) (extra : Bool)
  | fillBase (dest : B) (window : Recovery.Slot) (seedOffset : ℕ)
  | fillSupplier (source : B) (sourceSide : Bool) (sourceOffset : ℕ)
      (dest : B) (window : Recovery.Slot)
variable {B : Type*} [DecidableEq B]
def execute (x : Letters) (n k : ℕ) (header : B → Header)
    (mem : Bank B) : Instruction B → Option (Bank B)
  | .start source sourceSide sourceOffset dest destSide destOffset extra =>
    (PathMemory.readPath k (header source) (mem source) sourceSide sourceOffset k).bind
      fun bits =>
        let result := if destSide then
          ConcreteStart.startPositive k (header dest) destOffset bits extra (mem dest)
        else ConcreteStart.startNegative k (header dest) destOffset bits (mem dest)
        result.map (Function.update mem dest)
  | .fillBase dest window seedOffset =>
    (ConcreteFill.fillFromBase x n k (windowLength k) (mem dest)
      (negativeLength k (header dest))
      (windowStart (negativeExtra k (header dest)) window) seedOffset).map
      (Function.update mem dest)
  | .fillSupplier source sourceSide sourceOffset dest window =>
    (PathMemory.readPath k (header source) (mem source) sourceSide sourceOffset
      (windowLength k)).bind fun bits =>
        (writeBits (mem dest) (negativeLength k (header dest))
          (windowStart (negativeExtra k (header dest)) window) bits).map
          (Function.update mem dest)
def run (x : Letters) (n k : ℕ) (header : B → Header)
    (mem : Bank B) : List (Instruction B) → Option (Bank B)
  | [] => some mem
  | instruction :: rest =>
    (execute x n k header mem instruction).bind fun mem' => run x n k header mem' rest
def loadRoots (x : Letters) (n k : ℕ) (header : B → Header)
    (mem : Bank B) : List (B × ℕ) → Option (Bank B)
  | [] => some mem
  | (b, a) :: rest =>
    (ConcreteFill.loadRoot x n a (negativeLength k (header b))
      (mem b) (negativeLength k (header b))).bind fun t =>
        loadRoots x n k header (Function.update mem b t) rest
abbrev Output (k : ℕ) (header : B → Header) := ∀ b, PartialWords.Bits (negativeLength k (header b))
def finish [Fintype B] (k : ℕ) (header : B → Header) (mem : Bank B) :
    Option (Output k header) :=
  if ∀ b, readBits (mem b) 0 (negativeLength k (header b)) =
      some ((readBits (mem b) 0 (negativeLength k (header b))).getD (fun _ => false))
  then some (fun b => (readBits (mem b) 0 (negativeLength k (header b))).getD (fun _ => false))
  else none
def decode [Fintype B] (x : Letters) (n k : ℕ) (header : B → Header)
    (roots : List (B × ℕ)) (instructions : List (Instruction B)) :
    Option (Output k header) :=
  (loadRoots x n k header (fun _ => empty) roots).bind fun initial =>
    (run x n k header initial instructions).bind (finish k header)
end DeletionCode.ConcreteDecoder


