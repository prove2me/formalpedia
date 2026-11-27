-- Prove2me | Definitions.Def_TreeStack_HeightSource
-- name    : TreeStack_HeightSource
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:13:31.57458+00:00
-- url     : https://prove2.me/theorems/17bf6903-007a-579b-9d6f-b276dedae596
-- title:
--   Height Source
-- statement:
--   Definitions and structural lemmas for Height Source, from jfairfaxball-348 (jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees; see pinned Apache-2.0 LICENSE and README.md)'s pinned TreeStack: Csernák-Soukup stacking number equality stack(T) = estim(T) for nontrivial trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/HeightSource.lean

import Mathlib
import Definitions.Def_TreeStack_LeafSlack
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_auxEdgeContribution_reverse
import Theorems.Thm_TreeStack_OrientedBranch_boundaryParityWeight_parent
import Theorems.Thm_TreeStack_OrientedBranch_carrier_erase_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_defectiveSupportEdge_reverse_iff
import Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_empty
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_some
import Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_OrientedBranch_supportEdge_reverse_iff
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_of_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_self
import Theorems.Thm_TreeStack_RootTask_branch_parent
import Theorems.Thm_TreeStack_RootTask_branch_root
import Theorems.Thm_TreeStack_empty_ne_integer_zero
import Theorems.Thm_TreeStack_incidentBranch_parent
import Theorems.Thm_TreeStack_incidentBranch_root
import Theorems.Thm_TreeStack_mass_oneOn
import Theorems.Thm_TreeStack_mem_rootTasks
import Theorems.Thm_TreeStack_mem_support_iff
import Theorems.Thm_TreeStack_oneOn_apply
import Theorems.Thm_TreeStack_scoreDefect_nonneg_iff
attribute [local simp] TreeStack.F_three
attribute [local simp] TreeStack.F_two
attribute [local simp] TreeStack.MoveSignature.extend_count_same
attribute [local simp] TreeStack.MoveSignature.incoming_zero
attribute [local simp] TreeStack.MoveSignature.outgoing_zero
attribute [local simp] TreeStack.MoveSignature.zero_count
attribute [local simp] TreeStack.OrientedBranch.OccupiedChild.child_vertex
attribute [local simp] TreeStack.OrientedBranch.auxEdgeContribution_reverse
attribute [local simp] TreeStack.OrientedBranch.boundaryParityWeight_parent
attribute [local simp] TreeStack.OrientedBranch.carrier_erase_parent
attribute [local simp] TreeStack.OrientedBranch.childBranch_parent
attribute [local simp] TreeStack.OrientedBranch.childBranch_root
attribute [local simp] TreeStack.OrientedBranch.defectiveSupportEdge_reverse_iff
attribute [local simp] TreeStack.OrientedBranch.mem_occupiedChildTasks
attribute [local simp] TreeStack.OrientedBranch.messageContribution_empty
attribute [local simp] TreeStack.OrientedBranch.messageContribution_some
attribute [local simp] TreeStack.OrientedBranch.parent_mem_carrier
attribute [local simp] TreeStack.OrientedBranch.root_mem_carrier
attribute [local simp] TreeStack.OrientedBranch.root_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.root_ne_parent
attribute [local simp] TreeStack.OrientedBranch.supportEdge_reverse_iff
attribute [local simp] TreeStack.OrientedBranch.withBoundary_of_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.withBoundary_parent
attribute [local simp] TreeStack.OrientedBranch.withBoundary_self
attribute [local simp] TreeStack.RootTask.branch_parent
attribute [local simp] TreeStack.RootTask.branch_root
attribute [local simp] TreeStack.empty_ne_integer_zero
attribute [local simp] TreeStack.incidentBranch_parent
attribute [local simp] TreeStack.incidentBranch_root
attribute [local simp] TreeStack.mass_oneOn
attribute [local simp] TreeStack.mem_rootTasks
attribute [local simp] TreeStack.mem_support_iff
attribute [local simp] TreeStack.oneOn_apply
attribute [local simp] TreeStack.scoreDefect_nonneg_iff


set_option autoImplicit false
namespace TreeStack
open scoped BigOperators Classical
namespace OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
theorem exists_auxHeight_predecessor_of_pos
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hPos : 0 < auxHeight C ambientRoot hScores v) :
    ∃ u : V,
      AuxArrow (T := T) C ambientRoot u v ∧
        auxHeight C ambientRoot hScores u + 1 =
          auxHeight C ambientRoot hScores v := by
  let f : V → ℕ := fun u =>
    if h : AuxArrow (T := T) C ambientRoot u v then
      auxHeight C ambientRoot hScores u + 1
    else
      0
  have hNonempty : (Finset.univ : Finset V).Nonempty :=
    ⟨v, Finset.mem_univ v⟩
  rcases Finset.exists_mem_eq_sup (Finset.univ : Finset V) hNonempty f with
    ⟨u, -, hSup⟩
  have hEq :
      auxHeight C ambientRoot hScores v = f u := by
    rw [auxHeight]
    exact hSup
  by_cases hArrow : AuxArrow (T := T) C ambientRoot u v
  · refine ⟨u, hArrow, ?_⟩
    simpa [f, hArrow] using hEq.symm
  · have hZero : auxHeight C ambientRoot hScores v = 0 := by
      simpa [f, hArrow] using hEq
    omega
noncomputable def auxParent
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) : V :=
  if h : 0 < auxHeight C ambientRoot hScores v then
    Classical.choose
      (exists_auxHeight_predecessor_of_pos
        C ambientRoot hScores v h)
  else
    v
theorem auxParent_arrow_of_pos
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hPos : 0 < auxHeight C ambientRoot hScores v) :
    AuxArrow (T := T) C ambientRoot
      (auxParent C ambientRoot hScores v) v := by
  rw [auxParent, dif_pos hPos]
  exact
    (Classical.choose_spec
      (exists_auxHeight_predecessor_of_pos
        C ambientRoot hScores v hPos)).1
theorem auxParent_height_add_one
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hPos : 0 < auxHeight C ambientRoot hScores v) :
    auxHeight C ambientRoot hScores
        (auxParent C ambientRoot hScores v) + 1 =
      auxHeight C ambientRoot hScores v := by
  rw [auxParent, dif_pos hPos]
  exact
    (Classical.choose_spec
      (exists_auxHeight_predecessor_of_pos
        C ambientRoot hScores v hPos)).2
noncomputable def auxSourceWalk
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) : Σ r : V, T.graph.Walk v r :=
  if hZero : auxHeight C ambientRoot hScores v = 0 then
    ⟨v, SimpleGraph.Walk.nil⟩
  else
    let hPos : 0 < auxHeight C ambientRoot hScores v :=
      Nat.pos_of_ne_zero hZero
    let u := auxParent C ambientRoot hScores v
    let tailCert := auxSourceWalk C ambientRoot hScores u
    ⟨tailCert.1,
      SimpleGraph.Walk.cons
        (auxArrow_adj C ambientRoot
          (auxParent_arrow_of_pos C ambientRoot hScores v hPos)).symm
        tailCert.2⟩
termination_by auxHeight C ambientRoot hScores v
decreasing_by
  have hEq :=
    auxParent_height_add_one C ambientRoot hScores v
      (Nat.pos_of_ne_zero hZero)
  omega
noncomputable def auxSource
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) : V :=
  (auxSourceWalk C ambientRoot hScores v).1
noncomputable def auxWalk
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    T.graph.Walk v (auxSource C ambientRoot hScores v) :=
  (auxSourceWalk C ambientRoot hScores v).2
end OrientedBranch
end TreeStack


