-- Prove2me | Definitions.Def_TreeStack_Obstruction
-- name    : TreeStack_Obstruction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T22:44:31.025526+00:00
-- url     : https://prove2.me/theorems/ff39d049-4035-5ea1-bec9-b0db472e4a83
-- title:
--   Obstruction
-- statement:
--   Definitions and structural lemmas for Obstruction, from jfairfaxball-348 (jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees; see pinned Apache-2.0 LICENSE and README.md)'s pinned TreeStack: Csernák-Soukup stacking number equality stack(T) = estim(T) for nontrivial trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_OrientedBranch_Child_eq_of_vertex_eq
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_boundaryParityWeight_parent
import Theorems.Thm_TreeStack_OrientedBranch_carrier_erase_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_card_lt
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_vertices_disjoint
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_vertices_subset
import Theorems.Thm_TreeStack_OrientedBranch_exists_childBranch_mem_of_mem_vertices_ne_root
import Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_empty
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_some
import Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_parent_not_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_of_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_self
import Theorems.Thm_TreeStack_RootTask_branch_parent
import Theorems.Thm_TreeStack_RootTask_branch_root
import Theorems.Thm_TreeStack_empty_ne_integer_zero
import Theorems.Thm_TreeStack_exists_incidentBranch_mem_of_ne_root
import Theorems.Thm_TreeStack_incidentBranch_parent
import Theorems.Thm_TreeStack_incidentBranch_root
import Theorems.Thm_TreeStack_incidentBranch_vertices_disjoint
import Theorems.Thm_TreeStack_mass_oneOn
import Theorems.Thm_TreeStack_mem_rootTasks
import Theorems.Thm_TreeStack_mem_support_iff
import Theorems.Thm_TreeStack_oneOn_apply
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
attribute [local simp] TreeStack.OrientedBranch.mem_occupiedChildTasks
attribute [local simp] TreeStack.OrientedBranch.messageContribution_empty
attribute [local simp] TreeStack.OrientedBranch.messageContribution_some
attribute [local simp] TreeStack.OrientedBranch.parent_mem_carrier
attribute [local simp] TreeStack.OrientedBranch.root_mem_carrier
attribute [local simp] TreeStack.OrientedBranch.root_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.root_ne_parent
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


set_option autoImplicit false
namespace TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
noncomputable def obstruction (T : FiniteTree V) (r : V) : Configuration V := by
  classical
  exact fun v =>
    if v = r then
      sigma T r - 1
    else if v ∈ leafVertices T r then
      1
    else
      0
@[simp] theorem obstruction_root (T : FiniteTree V) (r : V) :
    obstruction T r r = sigma T r - 1 := by
  simp [obstruction]
namespace OrientedBranch
noncomputable def obstructionHeight (B : OrientedBranch T) : ℕ :=
  if hLeaf : T.graph.degree B.root = 1 then
    1
  else
    3 + 2 *
      ∑ v : V,
        if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
          obstructionHeight
            (B.childBranch
              { vertex := v
                adj := h.1
                ne_parent := h.2 })
        else
          0
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt
    { vertex := v
      adj := h.1
      ne_parent := h.2 }
noncomputable instance childFintype (B : OrientedBranch T) :
    Fintype B.Child :=
  Fintype.ofInjective
    (fun c : B.Child => c.vertex)
    (fun _ _ h => Child.eq_of_vertex_eq h)
abbrev ChildVertex (B : OrientedBranch T) :=
  Σ c : B.Child, {x : V // x ∈ (B.childBranch c).vertices}
abbrev ProperVertex (B : OrientedBranch T) :=
  {x : V // x ∈ B.vertices.erase B.root}
noncomputable def childVertexEquivProper (B : OrientedBranch T) :
    B.ChildVertex ≃ B.ProperVertex := by
  classical
  have hnotRoot :
      ∀ (c : B.Child) {x : V},
        x ∈ (B.childBranch c).vertices → x ≠ B.root := by
    intro c x hx hxr
    apply (B.childBranch c).parent_not_mem_vertices
    simpa [childBranch, hxr] using hx
  let chosen : B.ProperVertex → B.Child := fun x =>
    Classical.choose
      (B.exists_childBranch_mem_of_mem_vertices_ne_root
        (Finset.mem_erase.mp x.2).2
        (by
          intro h
          exact (Finset.mem_erase.mp x.2).1 h))
  have hchosen :
      ∀ x : B.ProperVertex,
        x.1 ∈ (B.childBranch (chosen x)).vertices := by
    intro x
    exact
      Classical.choose_spec
        (B.exists_childBranch_mem_of_mem_vertices_ne_root
          (Finset.mem_erase.mp x.2).2
          (by
            intro h
            exact (Finset.mem_erase.mp x.2).1 h))
  refine
    { toFun := fun z =>
        ⟨z.2.1,
          Finset.mem_erase.mpr
            ⟨hnotRoot z.1 z.2.2,
              B.childBranch_vertices_subset z.1 z.2.2⟩⟩
      invFun := fun x =>
        ⟨chosen x, ⟨x.1, hchosen x⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    let x : B.ProperVertex :=
      ⟨z.2.1,
        Finset.mem_erase.mpr
          ⟨hnotRoot z.1 z.2.2,
            B.childBranch_vertices_subset z.1 z.2.2⟩⟩
    have hc : chosen x = z.1 := by
      apply Child.eq_of_vertex_eq
      by_contra hne
      have hne' : z.1.vertex ≠ (chosen x).vertex := by
        intro h
        exact hne h.symm
      have hdisj :=
        B.childBranch_vertices_disjoint z.1 (chosen x) hne'
      exact
        (Finset.disjoint_left.mp hdisj) z.2.2 (hchosen x)
    apply Sigma.ext hc
    apply
      (Subtype.heq_iff_coe_eq
        (by
          intro y
          change
            y ∈ (B.childBranch (chosen x)).vertices ↔
              y ∈ (B.childBranch z.1).vertices
          rw [hc])).2
    rfl
  · intro x
    apply Subtype.ext
    rfl
noncomputable def childFinset (B : OrientedBranch T) : Finset V :=
  (T.graph.neighborFinset B.root).erase B.parent
@[simp] theorem mem_childFinset (B : OrientedBranch T) (v : V) :
    v ∈ B.childFinset ↔
      T.graph.Adj B.root v ∧ v ≠ B.parent := by
  classical
  simp [childFinset, and_left_comm, and_comm]
noncomputable def internalPotential (B : OrientedBranch T) : ℕ :=
  ∑ x ∈ B.vertices,
    if 1 < T.graph.degree x then
      T.graph.degree x * 2 ^ T.graph.dist B.root x
    else
      0
def reverseBranch (B : OrientedBranch T) : OrientedBranch T where
  root := B.parent
  parent := B.root
  adj := B.adj.symm
@[simp] theorem reverseBranch_root (B : OrientedBranch T) :
    B.reverseBranch.root = B.parent := rfl
@[simp] theorem reverseBranch_parent (B : OrientedBranch T) :
    B.reverseBranch.parent = B.root := rfl
@[simp] theorem reverseBranch_reverse (B : OrientedBranch T) :
    B.reverseBranch.reverseBranch = B := by
  cases B
  rfl
end OrientedBranch
abbrev RootNeighbor (T : FiniteTree V) (r : V) :=
  {u : V // T.graph.Adj u r}
namespace RootNeighbor
noncomputable def branch {T : FiniteTree V} {r : V}
    (n : RootNeighbor T r) : OrientedBranch T :=
  incidentBranch T r n.1 n.2
@[simp] theorem branch_root {T : FiniteTree V} {r : V}
    (n : RootNeighbor T r) :
    n.branch.root = n.1 := rfl
@[simp] theorem branch_parent {T : FiniteTree V} {r : V}
    (n : RootNeighbor T r) :
    n.branch.parent = r := rfl
end RootNeighbor
abbrev RootBranchVertex (T : FiniteTree V) (r : V) :=
  Σ n : RootNeighbor T r,
    {x : V // x ∈ n.branch.vertices}
abbrev RootProperVertex (r : V) :=
  {x : V // x ∈ (Finset.univ : Finset V).erase r}
noncomputable def rootBranchVertexEquivProper
    (T : FiniteTree V) (r : V) :
    RootBranchVertex T r ≃ RootProperVertex r := by
  classical
  have hnotRoot :
      ∀ (n : RootNeighbor T r) {x : V},
        x ∈ n.branch.vertices → x ≠ r := by
    intro n x hx hxr
    apply n.branch.parent_not_mem_vertices
    simpa [RootNeighbor.branch, incidentBranch, hxr] using hx
  have hex :
      ∀ x : RootProperVertex r,
        ∃ n : RootNeighbor T r, x.1 ∈ n.branch.vertices := by
    intro x
    have hxr : x.1 ≠ r := (Finset.mem_erase.mp x.2).1
    rcases exists_incidentBranch_mem_of_ne_root (T := T) r hxr with
      ⟨u, h, hx⟩
    exact ⟨⟨u, h⟩, hx⟩
  let chosen : RootProperVertex r → RootNeighbor T r :=
    fun x => Classical.choose (hex x)
  have hchosen :
      ∀ x : RootProperVertex r,
        x.1 ∈ (chosen x).branch.vertices := by
    intro x
    exact Classical.choose_spec (hex x)
  refine
    { toFun := fun z =>
        ⟨z.2.1,
          Finset.mem_erase.mpr
            ⟨hnotRoot z.1 z.2.2, Finset.mem_univ _⟩⟩
      invFun := fun x =>
        ⟨chosen x, ⟨x.1, hchosen x⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    let x : RootProperVertex r :=
      ⟨z.2.1,
        Finset.mem_erase.mpr
          ⟨hnotRoot z.1 z.2.2, Finset.mem_univ _⟩⟩
    have hn : chosen x = z.1 := by
      apply Subtype.ext
      by_contra hne
      have hne' : z.1.1 ≠ (chosen x).1 := by
        intro h
        exact hne h.symm
      have hdisj :=
        incidentBranch_vertices_disjoint
          (T := T) r z.1.2 (chosen x).2 hne'
      exact
        (Finset.disjoint_left.mp hdisj)
          z.2.2 (hchosen x)
    apply Sigma.ext hn
    apply
      (Subtype.heq_iff_coe_eq
        (by
          intro y
          change
            y ∈ (chosen x).branch.vertices ↔
              y ∈ z.1.branch.vertices
          rw [hn])).2
    rfl
  · intro x
    apply Subtype.ext
    rfl
namespace OrientedBranch
end OrientedBranch
end TreeStack


