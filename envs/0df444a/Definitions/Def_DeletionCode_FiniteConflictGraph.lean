-- Prove2me | Definitions.Def_DeletionCode_FiniteConflictGraph
-- name    : DeletionCode_FiniteConflictGraph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:32:51.606971+00:00
-- url     : https://prove2.me/theorems/99142086-41af-40b1-b67b-a2c3782a7ed1
-- title:
--   Finite Conflict Graph
-- statement:
--   Definitions and structural lemmas for Finite Conflict Graph, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteConflictGraph.lean

import Definitions.Def_DeletionCode_AlignmentTrace
import Definitions.Def_DeletionCode_BoundedWitnessWalk
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm

set_option autoImplicit true
namespace DeletionCode.FiniteConflictGraph
open HeaderRecovery AlignmentTrace EditAlignment
variable {n : ℕ} {H : Type*}
def Unique (k : ℕ) (x : Bits n) : Prop := Windows.KUnique (padBits x) n k
def Confusable (t : ℕ) (x y : Bits n) : Prop :=
  ∃ output : List Bool,
    WithinEdits t (List.ofFn x) output ∧ WithinEdits t (List.ofFn y) output
theorem Confusable.symm {t : ℕ} {x y : Bits n} (h : Confusable t x y) :
    Confusable t y x := by
  obtain ⟨output, hx, hy⟩ := h
  exact ⟨output, hy, hx⟩
def EditIndex (trace : Trace) (i : Fin trace.length) : Prop :=
  (trace.get i).isEdit = true
def Separated (B : ℕ) (trace : Trace) : Prop :=
  (∀ i : Fin trace.length, EditIndex trace i →
    B ≤ trace.matchedAnchor i.val ∧
      trace.matchedAnchor i.val + B ≤ trace.matchedCount) ∧
  ∀ i j : Fin trace.length, EditIndex trace i → EditIndex trace j →
    i.val < j.val → trace.matchedAnchor i.val + B ≤ trace.matchedAnchor j.val
def Exceptional (t k : ℕ) (label : Bits n → H) (x : Bits n) : Prop :=
  Unique k x ∧ ∃ y : Bits n, x ≠ y ∧ label x = label y ∧
    ∃ (d : ℕ) (trace : Trace),
      trace.source = List.ofFn x ∧ trace.target = List.ofFn y ∧
      trace.deletions = d ∧ trace.insertions = d ∧
      (d < t ∨ (d = t ∧ ¬ Separated (4 * windowLength k) trace))
def Vertex (t k : ℕ) (label : Bits n → H) :=
  {x : Bits n // Unique k x ∧ ¬ Exceptional t k label x}
instance vertexFinite (t k : ℕ) (label : Bits n → H) : Finite (Vertex t k label) := by
  unfold Vertex
  infer_instance
def graph (t k : ℕ) (label : Bits n → H) : SimpleGraph (Vertex t k label) where
  Adj x y := x.val ≠ y.val ∧ Confusable t x.val y.val ∧ label x.val = label y.val
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
  loopless := by
    constructor
    intro x h
    exact h.1 rfl
end DeletionCode.FiniteConflictGraph


