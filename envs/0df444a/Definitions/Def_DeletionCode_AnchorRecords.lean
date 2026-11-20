-- Prove2me | Definitions.Def_DeletionCode_AnchorRecords
-- name    : DeletionCode_AnchorRecords
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:53:12.069324+00:00
-- url     : https://prove2.me/theorems/f3cf54c6-a263-4b58-9bbb-9bd58d504c0d
-- title:
--   Anchor Records
-- statement:
--   Definitions and structural lemmas for Anchor Records, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AnchorRecords.lean

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_end
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_zero
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
import Theorems.Thm_DeletionCode_FiniteWalkRules_rational_step
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_empty
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_insert
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
import Theorems.Thm_DeletionCode_TraceEditData_split_column
attribute [local simp] DeletionCode.AlignmentTrace.Trace.matchedAnchor_end
attribute [local simp] DeletionCode.AlignmentTrace.Trace.matchedAnchor_zero
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_neg
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_zero
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.FiniteRelationBlocks.mem_selectedBlocks
attribute [local simp] DeletionCode.FiniteWalkRules.rational_step
attribute [local simp] DeletionCode.FiniteWalkRules.selectedRules_empty
attribute [local simp] DeletionCode.FiniteWalkRules.selectedRules_insert
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk


set_option autoImplicit true
namespace DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData
abbrev Packet := ℕ × (Bool × Bool)
def payload : Column → Bool × Bool
  | .matched _ => (false, false)
  | .deletion _ => (false, false)
  | .insertion bit => (true, bit)
def encodeFrom (matchedBefore : ℕ) : Trace → List Packet
  | [] => []
  | .matched _ :: rest => encodeFrom (matchedBefore + 1) rest
  | .deletion _ :: rest => (matchedBefore, (false, false)) :: encodeFrom matchedBefore rest
  | .insertion bit :: rest => (matchedBefore, (true, bit)) :: encodeFrom matchedBefore rest
def encode (trace : Trace) : List Packet := encodeFrom 0 trace
def decodeFrom (matchedBefore : ℕ) (source : List Bool) : List Packet → List Bool
  | [] => source
  | (anchor, (side, bit)) :: rest =>
      if side then
        source.take (anchor - matchedBefore) ++
          bit :: decodeFrom anchor (source.drop (anchor - matchedBefore)) rest
      else
        source.take (anchor - matchedBefore) ++
          decodeFrom anchor (source.drop (anchor - matchedBefore + 1)) rest
def decode (source : List Bool) (packets : List Packet) : List Bool :=
  decodeFrom 0 source packets
theorem encodeFrom_append (left right : Trace) (m : ℕ) :
    encodeFrom m (left ++ right) =
      encodeFrom m left ++ encodeFrom (m + left.matchedCount) right := by
  induction left generalizing m with
  | nil => simp [encodeFrom, Trace.matchedCount]
  | cons col rest ih =>
    cases col <;> simp [encodeFrom, Trace.matchedCount, ih,
      Nat.add_assoc, Nat.add_comm]
theorem encode_split_edit (trace : Trace) (c : EditColumn trace) :
    encode trace = encode (trace.take c.val.val) ++
      (trace.matchedAnchor c.val.val, payload (column trace c)) ::
        encodeFrom (trace.matchedAnchor c.val.val) (trace.drop (c.val.val + 1)) := by
  have hs := congrArg (encodeFrom 0) (split_column trace c)
  rw [encodeFrom_append] at hs
  simp only [Nat.zero_add] at hs
  rcases column_cases trace c with ⟨bit, hc⟩ | ⟨bit, hc⟩
  · simpa only [encode, Trace.matchedAnchor, hc, encodeFrom, payload] using hs
  · simpa only [encode, Trace.matchedAnchor, hc, encodeFrom, payload] using hs
def recordRank (trace : Trace) (c : EditColumn trace) : ℕ :=
  (encode (trace.take c.val.val)).length
theorem recordRank_lt (trace : Trace) (c : EditColumn trace) :
    recordRank trace c < (encode trace).length := by
  have h := congrArg List.length (encode_split_edit trace c)
  simp only [List.length_append, List.length_cons] at h
  unfold recordRank
  omega
def recordIndex (trace : Trace) (c : EditColumn trace) : Fin (encode trace).length :=
  ⟨recordRank trace c, recordRank_lt trace c⟩
end DeletionCode.AnchorRecords


