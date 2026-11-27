-- Prove2me | Definitions.Def_TreeStack_GlobalCharge
-- name    : TreeStack_GlobalCharge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:11:46.89532+00:00
-- url     : https://prove2.me/theorems/d651d236-df93-4cf4-9e96-7a640e301869
-- title:
--   Global Charge
-- statement:
--   Definitions and structural lemmas for Global Charge, from jfairfaxball-348 (jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees; see pinned Apache-2.0 LICENSE and README.md)'s pinned TreeStack: Csernák-Soukup stacking number equality stack(T) = estim(T) for nontrivial trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
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
theorem exists_edgeDart (e : T.graph.edgeFinset) :
    ∃ d : T.graph.Dart, d.edge = e.1 := by
  rcases Sym2.mk_surjective e.1 with ⟨⟨u, v⟩, huv⟩
  have hedge : e.1 ∈ T.graph.edgeSet :=
    SimpleGraph.mem_edgeFinset.mp e.2
  have hadj : T.graph.Adj u v := by
    rw [← huv] at hedge
    simpa using hedge
  refine ⟨⟨(u, v), hadj⟩, ?_⟩
  simpa using huv
noncomputable def edgeDart (e : T.graph.edgeFinset) : T.graph.Dart :=
  Classical.choose (exists_edgeDart (T := T) e)
@[simp] theorem edgeDart_edge (e : T.graph.edgeFinset) :
    (edgeDart (T := T) e).edge = e.1 :=
  Classical.choose_spec (exists_edgeDart (T := T) e)
noncomputable def edgeBranch (e : T.graph.edgeFinset) : OrientedBranch T :=
  incidentBranch T (edgeDart (T := T) e).snd
    (edgeDart (T := T) e).fst (edgeDart (T := T) e).adj
@[simp] theorem edgeBranch_root (e : T.graph.edgeFinset) :
    (edgeBranch (T := T) e).root = (edgeDart (T := T) e).fst := rfl
@[simp] theorem edgeBranch_parent (e : T.graph.edgeFinset) :
    (edgeBranch (T := T) e).parent = (edgeDart (T := T) e).snd := rfl
noncomputable def edgeOwner (ambientRoot : V)
    (e : T.graph.edgeFinset) : V :=
  (edgeBranch (T := T) e).rootedOwner ambientRoot
noncomputable def auxWeightedMass
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) : ℤ :=
  ∑ v : V, auxWeightInt C ambientRoot hScores v * (C v : ℤ)
noncomputable def auxDefectBudget
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) : ℤ :=
  ∑ v : V,
    auxWeightInt C ambientRoot hScores v * scoreDefect T C v
noncomputable def auxDegreePotential
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) : ℤ :=
  ∑ v : V, (T.graph.degree v : ℤ) *
    auxWeightInt C ambientRoot hScores v
noncomputable def edgeSeparatedCharge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (e : T.graph.edgeFinset) : ℤ :=
  retainedDefectCharge C ambientRoot hScores (edgeBranch e) +
    emptyBoundaryCharge C ambientRoot hScores (edgeBranch e)
noncomputable def dartOfEdgeBool
    (p : T.graph.edgeFinset × Bool) : T.graph.Dart :=
  if p.2 then (edgeDart (T := T) p.1).symm else edgeDart (T := T) p.1
@[simp] theorem dartOfEdgeBool_edge
    (p : T.graph.edgeFinset × Bool) :
    (dartOfEdgeBool (T := T) p).edge = p.1.1 := by
  rcases p with ⟨e, b⟩
  cases b <;> simp [dartOfEdgeBool, edgeDart_edge]
theorem dartOfEdgeBool_injective :
    Function.Injective (dartOfEdgeBool (T := T)) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ h
  have hEdge : e = f := by
    apply Subtype.ext
    have h' := congrArg SimpleGraph.Dart.edge h
    simpa using h'
  subst f
  cases b <;> cases c
  · rfl
  · have h' : edgeDart (T := T) e =
        (edgeDart (T := T) e).symm := by
      simpa [dartOfEdgeBool] using h
    exact ((edgeDart (T := T) e).symm_ne h'.symm).elim
  · have h' : (edgeDart (T := T) e).symm =
        edgeDart (T := T) e := by
      simpa [dartOfEdgeBool] using h
    exact ((edgeDart (T := T) e).symm_ne h').elim
  · rfl
theorem dartOfEdgeBool_surjective :
    Function.Surjective (dartOfEdgeBool (T := T)) := by
  intro d
  let e : T.graph.edgeFinset :=
    ⟨d.edge, SimpleGraph.mem_edgeFinset.mpr d.edge_mem⟩
  have hSameEdge : (edgeDart (T := T) e).edge = d.edge := by
    exact edgeDart_edge (T := T) e
  rcases (SimpleGraph.dart_edge_eq_iff (edgeDart (T := T) e) d).mp hSameEdge with
    h | h
  · refine ⟨(e, false), ?_⟩
    simpa [dartOfEdgeBool] using h
  · refine ⟨(e, true), ?_⟩
    simp [dartOfEdgeBool, h]
noncomputable def edgeBoolEquivDart :
    T.graph.edgeFinset × Bool ≃ T.graph.Dart :=
  Equiv.ofBijective (dartOfEdgeBool (T := T))
    ⟨dartOfEdgeBool_injective (T := T),
      dartOfEdgeBool_surjective (T := T)⟩
@[simp] theorem edgeBoolEquivDart_apply
    (p : T.graph.edgeFinset × Bool) :
    edgeBoolEquivDart (T := T) p = dartOfEdgeBool (T := T) p :=
  rfl
def dartEquivHeadNeighbor :
    T.graph.Dart ≃ Σ v : V, T.graph.neighborSet v where
  toFun d := ⟨d.snd, ⟨d.fst, d.adj.symm⟩⟩
  invFun p := ⟨(p.2.1, p.1), p.2.2.symm⟩
  left_inv d := by ext <;> rfl
  right_inv p := by cases p; rfl
noncomputable def auxDartMessageTerm
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (d : T.graph.Dart) : ℤ :=
  auxWeightInt C ambientRoot hScores d.snd *
    rootMessageTerm T C d.snd d.fst
set_option maxHeartbeats 800000
set_option maxHeartbeats 200000
end OrientedBranch
end TreeStack


