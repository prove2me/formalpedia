-- Prove2me | Definitions.Def_DeletionCode_RecordSerialization
-- name    : DeletionCode_RecordSerialization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:16:18.806932+00:00
-- url     : https://prove2.me/theorems/7148ac74-c122-490a-a1c6-7e024a6f0ebc
-- title:
--   Record Serialization
-- statement:
--   Definitions and structural lemmas for Record Serialization, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordSerialization.lean

import Definitions.Def_DeletionCode_RecordBounds
import Definitions.Def_DeletionCode_RecordPacking
set_option autoImplicit true
namespace DeletionCode.RecordSerialization
open Windows HeaderRecovery ConcreteDecoder DescriptionCount RecordCodec
open RecordPacking GeneratingModel
structure RecoveredData (ν : ℕ) where
  header : Fin ν → Header
  words : Fin ν → List Bool
def dataOfOutput {ν : ℕ} (k : ℕ) (header : Fin ν → Header) (output : Output k header) :
    RecoveredData ν := ⟨header, fun b => List.ofFn (output b)⟩
def dataOfFamily {ν k : ℕ} (E : EditedFamily (Fin ν) k) : RecoveredData ν :=
  dataOfOutput k E.header (fun b i => negativePath k (E.header b) (E.long b) i.val)
def encodeTotal (L ν : ℕ) (hL : 1 ≤ L) (hν : 1 ≤ ν)
    (instruction : Instruction (Fin ν)) : Row L ν :=
  if hb : InstructionBounded L instruction then encodeInstruction L ν hL hν instruction hb
  else zeroRow L ν hL hν
def rootVectors (n ν c : ℕ) (roots : List (Fin ν × ℕ))
    (hlen : roots.length = c) (hpos : ∀ b a, (b, a) ∈ roots → a < n) :
    (Fin c → Fin n) × (Fin c → Fin ν) :=
  ⟨fun i =>
      let r := roots.get ⟨i.val, by omega⟩
      ⟨r.2, hpos r.1 r.2 (List.get_mem _ _)⟩,
    fun i => (roots.get ⟨i.val, by omega⟩).1⟩
def rootsOfVectors {n ν c : ℕ} (positions : Fin c → Fin n) (names : Fin c → Fin ν) :
    List (Fin ν × ℕ) := List.ofFn (fun i => (names i, (positions i).val))
def encodeDescription (n k ν c : ℕ) (hν : 1 ≤ ν)
    (header : Fin ν → Header)
    (hlo : ∀ b, 1 ≤ (header b).rho) (hhi : ∀ b, (header b).rho ≤ windowLength k)
    (roots : List (Fin ν × ℕ)) (hroots : roots.length = c)
    (hpos : ∀ b a, (b, a) ∈ roots → a < n)
    (instructions : List (Instruction (Fin ν))) : Description n (windowLength k) ν c :=
  let hL : 1 ≤ windowLength k := by unfold windowLength; omega
  let rv := rootVectors n ν c roots hroots hpos
  ⟨rv.1, (fun b => encodeHeader (windowLength k) (header b) (hlo b) (hhi b)), rv.2,
    pack (zeroRow (windowLength k) ν hL hν)
      (instructions.map (encodeTotal (windowLength k) ν hL hν)) (4 * ν)⟩
def decodeDescription (x : Letters) (n k ν c : ℕ) (hν : 1 ≤ ν)
    (description : Description n (windowLength k) ν c) : Option (RecoveredData ν) :=
  let header := fun b => decodeHeader (description.2.1 b)
  let roots := rootsOfVectors description.1 description.2.2.1
  (unpack (decodeInstruction (windowLength k) ν hν) (4 * ν) description.2.2.2).bind
    fun instructions => (decode x n k header roots instructions).map (dataOfOutput k header)
end DeletionCode.RecordSerialization


