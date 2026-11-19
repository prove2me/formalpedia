-- Prove2me | Definitions.Def_DeletionCode_DecoderExamples
-- name    : DeletionCode_DecoderExamples
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:09:15.845547+00:00
-- url     : https://prove2.me/theorems/5e1c3e4f-1879-4fea-bb98-d3c995388dd8
-- title:
--   Decoder Examples
-- statement:
--   Definitions and structural lemmas for Decoder Examples, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/DecoderExamples.lean

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
set_option autoImplicit true
namespace DeletionCode.DecoderExamples
open Windows PartialWords
def sampleWord : Letters :=
  fun i => [false, false, false, true, false, true, true, true, false, false].getD i false
def sampleSeed : Bits 3 := fun i => i.val != 1
def sampleMemory : Memory := putBits empty 1 sampleSeed
def crossingHeader : HeaderRecovery.Header := ⟨.insertion, 1, true⟩
def crossingLong : Letters := fun i => i == 5
end DeletionCode.DecoderExamples


