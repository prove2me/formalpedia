-- Prove2me | Definitions.Def_DeletionCode_TraceEditData
-- name    : DeletionCode_TraceEditData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:43:13.214189+00:00
-- url     : https://prove2.me/theorems/a1ca57c2-314b-4379-990b-cecc7ec67779
-- title:
--   Trace Edit Data
-- statement:
--   Definitions and structural lemmas for Trace Edit Data, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceEditData.lean

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_end
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_zero
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
import Theorems.Thm_DeletionCode_EditAlignment_Script_trans
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
import Theorems.Thm_DeletionCode_FiniteWalkRules_rational_step
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_empty
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_insert
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
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
namespace DeletionCode.TraceEditData
open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators
def EditColumn (trace : Trace) := {i : Fin trace.length // EditIndex trace i}
instance editColumnFintype (trace : Trace) : Fintype (EditColumn trace) := by
  unfold EditColumn EditIndex
  infer_instance
def column (trace : Trace) (c : EditColumn trace) : Column := trace.get c.val
def position (trace : Trace) (c : EditColumn trace) : ℕ := trace.sourcePosition c.val.val
theorem column_isEdit (trace : Trace) (c : EditColumn trace) :
    (column trace c).isEdit = true := c.property
theorem column_cases (trace : Trace) (c : EditColumn trace) :
    (∃ bit, column trace c = .deletion bit) ∨ (∃ bit, column trace c = .insertion bit) := by
  have h := column_isEdit trace c
  cases hc : column trace c with
  | matched bit => simp only [hc, Column.isEdit, Bool.false_eq_true] at h
  | deletion bit => exact Or.inl ⟨bit, rfl⟩
  | insertion bit => exact Or.inr ⟨bit, rfl⟩
def orientation (trace : Trace) (c : EditColumn trace) : Orientation :=
  match column trace c with
  | .matched _ => .deletion
  | .deletion _ => .deletion
  | .insertion _ => .insertion
def bit (trace : Trace) (c : EditColumn trace) : Bool :=
  match column trace c with
  | .matched b => b
  | .deletion b => b
  | .insertion b => b
theorem orientation_of_deletion (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .deletion b) : orientation trace c = .deletion := by
  simp [orientation, hc]
theorem orientation_of_insertion (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .insertion b) : orientation trace c = .insertion := by
  simp [orientation, hc]
def oneEditTarget (trace : Trace) (c : EditColumn trace) : List Bool :=
  match orientation trace c with
  | .deletion => trace.source.eraseIdx (position trace c)
  | .insertion => trace.source.take (position trace c) ++
      bit trace c :: trace.source.drop (position trace c)
def isDeletion : Column → Bool
  | .deletion _ => true
  | _ => false
def isInsertion : Column → Bool
  | .insertion _ => true
  | _ => false
theorem isDeletion_edit (col : Column) (h : isDeletion col = true) : col.isEdit = true := by
  cases col <;> simp_all only [isDeletion, Column.isEdit, Bool.false_eq_true]
theorem isInsertion_edit (col : Column) (h : isInsertion col = true) : col.isEdit = true := by
  cases col <;> simp_all only [isInsertion, Column.isEdit, Bool.false_eq_true]
theorem orientation_eq_deletion_iff (trace : Trace) (c : EditColumn trace) :
    orientation trace c = .deletion ↔ isDeletion (column trace c) = true := by
  rcases column_cases trace c with ⟨b, hc⟩ | ⟨b, hc⟩
  · simp only [orientation_of_deletion trace c b hc, hc, isDeletion]
  · simp only [orientation_of_insertion trace c b hc, hc, isDeletion, reduceCtorEq,
      Bool.false_eq_true]
theorem orientation_eq_insertion_iff (trace : Trace) (c : EditColumn trace) :
    orientation trace c = .insertion ↔ isInsertion (column trace c) = true := by
  rcases column_cases trace c with ⟨b, hc⟩ | ⟨b, hc⟩
  · simp only [orientation_of_deletion trace c b hc, hc, isInsertion, reduceCtorEq,
      Bool.false_eq_true]
  · simp only [orientation_of_insertion trace c b hc, hc, isInsertion]
theorem card_column_predicate (trace : Trace) (p : Column → Bool) :
    Fintype.card {i : Fin trace.length // p (trace.get i) = true} = trace.countP p := by
  classical
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  induction trace with
  | nil => simp
  | cons col rest ih =>
    simp only [List.length_cons, Fin.sum_univ_succ, List.get_cons_zero,
      List.get_cons_succ', List.countP_cons, ih]
    by_cases hp : p col = true <;> simp_all [Nat.add_comm]
theorem countP_isEdit (trace : Trace) :
    trace.countP Column.isEdit = trace.deletions + trace.insertions := by
  induction trace with
  | nil => rfl
  | cons col rest ih =>
    cases col <;>
      simp only [List.countP_cons, Column.isEdit, Bool.false_eq_true,
        ite_true, ite_false, Trace.deletions, Trace.insertions, ih] <;> omega
theorem card_editColumn (trace : Trace) :
    Fintype.card (EditColumn trace) = trace.deletions + trace.insertions :=
  (card_column_predicate trace Column.isEdit).trans (countP_isEdit trace)
def deletionColumnEquiv (trace : Trace) :
    {c : EditColumn trace // orientation trace c = .deletion} ≃
      {i : Fin trace.length // isDeletion (trace.get i) = true} where
  toFun c := ⟨c.val.val, (orientation_eq_deletion_iff trace c.val).mp c.property⟩
  invFun i := ⟨⟨i.val, isDeletion_edit (trace.get i.val) i.property⟩,
    (orientation_eq_deletion_iff trace _).mpr i.property⟩
  left_inv c := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; rfl
def insertionColumnEquiv (trace : Trace) :
    {c : EditColumn trace // orientation trace c = .insertion} ≃
      {i : Fin trace.length // isInsertion (trace.get i) = true} where
  toFun c := ⟨c.val.val, (orientation_eq_insertion_iff trace c.val).mp c.property⟩
  invFun i := ⟨⟨i.val, isInsertion_edit (trace.get i.val) i.property⟩,
    (orientation_eq_insertion_iff trace _).mpr i.property⟩
  left_inv c := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; rfl
noncomputable def editEquiv (trace : Trace) (t : ℕ)
    (hdel : trace.deletions = t) (hins : trace.insertions = t) :
    Fin (2 * t) ≃ EditColumn trace :=
  (Fintype.equivFinOfCardEq (show Fintype.card (EditColumn trace) = 2 * t by
    rw [card_editColumn, hdel, hins]
    omega)).symm
def sourcePrefix (trace : Trace) (c : EditColumn trace) : List Bool :=
  Trace.source (trace.take c.val.val)
def sourceSuffix (trace : Trace) (c : EditColumn trace) : List Bool :=
  Trace.source (trace.drop (c.val.val + 1))
def targetPrefix (trace : Trace) (c : EditColumn trace) : List Bool :=
  Trace.target (trace.take c.val.val)
def targetSuffix (trace : Trace) (c : EditColumn trace) : List Bool :=
  Trace.target (trace.drop (c.val.val + 1))
end DeletionCode.TraceEditData


