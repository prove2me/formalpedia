-- Prove2me | Definitions.Def_TreeStack_Auxiliary
-- name    : TreeStack_Auxiliary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:06:05.558441+00:00
-- url     : https://prove2.me/theorems/4944b04f-903d-5955-b6ef-c04ce7a57803
-- title:
--   Auxiliary
-- statement:
--   Definitions and structural lemmas for Auxiliary, from jfairfaxball-348 (jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees; see pinned Apache-2.0 LICENSE and README.md)'s pinned TreeStack: Csernák-Soukup stacking number equality stack(T) = estim(T) for nontrivial trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean

import Mathlib
import Definitions.Def_TreeStack_DefectCharge
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_boundaryParityWeight_parent
import Theorems.Thm_TreeStack_OrientedBranch_carrier_erase_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_defectiveSupportEdge_reverse_iff
import Theorems.Thm_TreeStack_OrientedBranch_edge_leaving_vertices_eq_boundary
import Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_empty
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_some
import Theorems.Thm_TreeStack_OrientedBranch_not_defectArrow_reverse
import Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_parent_not_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_OrientedBranch_rootedOwner_reverse
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
@[simp] theorem incidentBranch_reverse
    (u v : V) (h : T.graph.Adj u v) :
    incidentBranch T u v h.symm =
      (incidentBranch T v u h).reverseBranch := by
  rfl
def TwoNegativeOwnerArrow
    (C : Configuration V) (ambientRoot : V) (B : OrientedBranch T) : Prop :=
  B.DefectiveSupportEdge C ∧
    messageContribution (branchMessage C B) < 0 ∧
    messageContribution (branchMessage C B.reverseBranch) < 0 ∧
    B.parent = B.rootedOwner ambientRoot
theorem not_twoNegativeOwnerArrow_reverse
    (C : Configuration V) (ambientRoot : V) (B : OrientedBranch T)
    (hArrow : B.TwoNegativeOwnerArrow C ambientRoot) :
    ¬ B.reverseBranch.TwoNegativeOwnerArrow C ambientRoot := by
  intro hReverse
  have hParentOwner :
      B.parent = B.rootedOwner ambientRoot :=
    hArrow.2.2.2
  have hRootOwner :
      B.root = B.rootedOwner ambientRoot := by
    have h := hReverse.2.2.2
    simpa [rootedOwner_reverse] using h
  exact B.root_ne_parent (hRootOwner.trans hParentOwner.symm)
def AuxArrow
    (C : Configuration V) (ambientRoot : V) (u v : V) : Prop :=
  ∃ h : T.graph.Adj u v,
    let B := incidentBranch T v u h
    B.DefectArrow C ∨
      B.TwoNegativeOwnerArrow C ambientRoot
@[simp] theorem incidentBranch_self
    (B : OrientedBranch T) :
    incidentBranch T B.parent B.root B.adj = B := by
  cases B
  rfl
@[simp] theorem incidentBranch_reverse_self
    (B : OrientedBranch T) :
    incidentBranch T B.root B.parent B.adj.symm = B.reverseBranch := by
  cases B
  rfl
theorem auxArrow_adj
    (C : Configuration V) (ambientRoot : V) {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    T.graph.Adj u v := by
  rcases hArrow with ⟨h, _⟩
  exact h
theorem not_auxArrow_reverse
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    ¬ AuxArrow (T := T) C ambientRoot v u := by
  intro hReverse
  rcases hArrow with ⟨huv, hForwardState⟩
  rcases hReverse with ⟨hvu, hReverseState⟩
  let B : OrientedBranch T := incidentBranch T v u huv
  have hRevBranch :
      incidentBranch T u v hvu = B.reverseBranch := by
    have hp : hvu = huv.symm := Subsingleton.elim _ _
    subst hvu
    rfl
  dsimp only at hForwardState hReverseState
  change
    B.DefectArrow C ∨
      B.TwoNegativeOwnerArrow C ambientRoot at hForwardState
  rw [hRevBranch] at hReverseState
  rcases hForwardState with hForward | hForward
  · rcases hReverseState with hReverse | hReverse
    · exact
        (B.not_defectArrow_reverse C hForward hScores)
          hReverse
    · exact
        (not_lt_of_ge hForward.2)
          hReverse.2.2.1
  · rcases hReverseState with hReverse | hReverse
    · exact
        (not_lt_of_ge hReverse.2)
          hForward.2.2.1
    · exact
        (B.not_twoNegativeOwnerArrow_reverse C ambientRoot hForward)
          hReverse
theorem auxArrow_no_reflTransGen_reverse
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    ¬ Relation.ReflTransGen
        (AuxArrow (T := T) C ambientRoot) v u := by
  intro hReturn
  let B : OrientedBranch T :=
    incidentBranch T v u (auxArrow_adj C ambientRoot hArrow)
  have hOutside :
      ∀ {x : V},
        Relation.ReflTransGen
            (AuxArrow (T := T) C ambientRoot) v x →
          x ∉ B.vertices := by
    intro x hx
    induction hx with
    | refl =>
        simpa [B] using B.parent_not_mem_vertices
    | tail hReach hStep ih =>
        intro hxIn
        have hAdj :=
          (auxArrow_adj C ambientRoot hStep).symm
        have hEdge :=
          B.edge_leaving_vertices_eq_boundary hxIn ih hAdj
        rw [Sym2.eq_iff] at hEdge
        rcases hEdge with hEdge | hEdge
        · have hReverse :
              AuxArrow (T := T) C ambientRoot v u := by
            rcases hEdge with ⟨hRoot, hParent⟩
            subst_vars
            simpa [B] using hStep
          exact
            (not_auxArrow_reverse C ambientRoot hScores hArrow)
              hReverse
        · have : B.parent ∈ B.vertices := by
            rw [← hEdge.1]
            exact hxIn
          exact B.parent_not_mem_vertices this
  have huOutside := hOutside hReturn
  exact huOutside (by simpa [B] using B.root_mem_vertices)
theorem auxArrow_transGen_irrefl
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    ¬ Relation.TransGen
        (AuxArrow (T := T) C ambientRoot) v v := by
  intro hCycle
  rcases Relation.TransGen.head'_iff.mp hCycle with
    ⟨u, hFirst, hReturn⟩
  exact
    (auxArrow_no_reflTransGen_reverse
      C ambientRoot hScores hFirst) hReturn
noncomputable def auxPred
    (C : Configuration V) (ambientRoot : V) (v : V) : Finset V :=
  (Finset.univ : Finset V).filter fun u =>
    Relation.TransGen (AuxArrow (T := T) C ambientRoot) u v
@[simp] theorem mem_auxPred
    (C : Configuration V) (ambientRoot : V) (u v : V) :
    u ∈ auxPred (T := T) C ambientRoot v ↔
      Relation.TransGen (AuxArrow (T := T) C ambientRoot) u v := by
  simp [auxPred]
theorem auxPred_ssubset_of_auxArrow
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    auxPred (T := T) C ambientRoot u ⊂
      auxPred (T := T) C ambientRoot v := by
  have hSubset :
      auxPred (T := T) C ambientRoot u ⊆
        auxPred (T := T) C ambientRoot v := by
    intro x hx
    rw [mem_auxPred] at hx ⊢
    exact Relation.TransGen.tail hx hArrow
  rw [Finset.ssubset_iff_of_subset hSubset]
  refine ⟨u, ?_, ?_⟩
  · rw [mem_auxPred]
    exact Relation.TransGen.single hArrow
  · rw [mem_auxPred]
    exact auxArrow_transGen_irrefl C ambientRoot hScores u
noncomputable def auxRank
    (C : Configuration V) (ambientRoot : V) (v : V) : ℕ :=
  (auxPred (T := T) C ambientRoot v).card
theorem auxRank_lt_of_auxArrow
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    auxRank (T := T) C ambientRoot u <
      auxRank (T := T) C ambientRoot v := by
  exact Finset.card_lt_card
    (auxPred_ssubset_of_auxArrow
      C ambientRoot hScores hArrow)
noncomputable def auxHeight
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) : ℕ :=
  (Finset.univ : Finset V).sup fun u =>
    if h : AuxArrow (T := T) C ambientRoot u v then
      auxHeight C ambientRoot hScores u + 1
    else
      0
termination_by auxRank (T := T) C ambientRoot v
decreasing_by
  exact auxRank_lt_of_auxArrow C ambientRoot hScores h
noncomputable def auxWeight
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) : ℕ :=
  2 ^ auxHeight C ambientRoot hScores v
noncomputable def auxWeightInt
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) : ℤ :=
  (auxWeight C ambientRoot hScores v : ℤ)
end OrientedBranch
end TreeStack


