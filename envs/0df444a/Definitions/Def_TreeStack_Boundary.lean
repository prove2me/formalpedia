-- Prove2me | Definitions.Def_TreeStack_Boundary
-- name    : TreeStack_Boundary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T22:25:22.649848+00:00
-- url     : https://prove2.me/theorems/0857f028-6271-5a3d-b9fd-86c2a105b905
-- title:
--   Boundary
-- statement:
--   Definitions and structural lemmas for Boundary, from jfairfaxball-348 (jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees; see pinned Apache-2.0 LICENSE and README.md)'s pinned TreeStack: Csernák-Soukup stacking number equality stack(T) = estim(T) for nontrivial trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_empty
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_some
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_empty_ne_integer_zero
import Theorems.Thm_TreeStack_mass_oneOn
import Theorems.Thm_TreeStack_mem_support_iff
import Theorems.Thm_TreeStack_oneOn_apply
attribute [local simp] TreeStack.F_three
attribute [local simp] TreeStack.F_two
attribute [local simp] TreeStack.OrientedBranch.childBranch_parent
attribute [local simp] TreeStack.OrientedBranch.childBranch_root
attribute [local simp] TreeStack.OrientedBranch.messageContribution_empty
attribute [local simp] TreeStack.OrientedBranch.messageContribution_some
attribute [local simp] TreeStack.OrientedBranch.root_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.root_ne_parent
attribute [local simp] TreeStack.empty_ne_integer_zero
attribute [local simp] TreeStack.mass_oneOn
attribute [local simp] TreeStack.mem_support_iff
attribute [local simp] TreeStack.oneOn_apply


set_option autoImplicit false
namespace TreeStack
open scoped BigOperators Classical
structure MoveSignature {V : Type*} [Fintype V] (T : FiniteTree V) where
  count : V → V → ℕ
  supported : ∀ {u v}, 0 < count u v → T.graph.Adj u v
namespace MoveSignature
variable {V : Type*} [Fintype V] {T : FiniteTree V}
def incoming (m : MoveSignature T) (v : V) : ℕ :=
  ∑ u, m.count u v
def outgoing (m : MoveSignature T) (v : V) : ℕ :=
  ∑ w, m.count v w
def BalancesAt (m : MoveSignature T) (C : Configuration V) (v : V) : Prop :=
  (C v : ℤ) + (m.incoming v : ℤ) - 2 * (m.outgoing v : ℤ) = 0
def zero (T : FiniteTree V) : MoveSignature T where
  count := fun _ _ => 0
  supported := by simp
def extend [DecidableEq V] (m : MoveSignature T) (u v : V)
    (huv : T.graph.Adj u v) : MoveSignature T where
  count := fun a b => m.count a b + if a = u ∧ b = v then 1 else 0
  supported := by
    intro a b hpos
    by_cases hnew : a = u ∧ b = v
    · rcases hnew with ⟨rfl, rfl⟩
      exact huv
    · have hm : 0 < m.count a b := by
        simpa [hnew] using hpos
      exact m.supported hm
end MoveSignature
section TaskScheduling
variable {α : Type*}
def taskGainSum (gain : α → ℤ) : List α → ℤ
  | [] => 0
  | t :: ts => gain t + taskGainSum gain ts
def TaskScheduleSafe (gain : α → ℤ) : ℤ → List α → Prop
  | _, [] => True
  | a, t :: ts =>
      0 < a + gain t ∧
        TaskScheduleSafe gain (a + gain t) ts
def positiveTasks (gain : α → ℤ) (tasks : List α) : List α :=
  tasks.filter fun t => 0 < gain t
def zeroTasks (gain : α → ℤ) (tasks : List α) : List α :=
  tasks.filter fun t => gain t = 0
def negativeTasks (gain : α → ℤ) (tasks : List α) : List α :=
  tasks.filter fun t => gain t < 0
def orderedTasks (gain : α → ℤ) (tasks : List α) : List α :=
  positiveTasks gain tasks ++
    (zeroTasks gain tasks ++ negativeTasks gain tasks)
end TaskScheduling
namespace OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
noncomputable def carrier (B : OrientedBranch T) : Finset V :=
  insert B.parent B.vertices
def MoveSignature.SupportedOn (m : MoveSignature T) (B : OrientedBranch T) : Prop :=
  ∀ ⦃u v⦄, 0 < m.count u v → u ∈ B.carrier ∧ v ∈ B.carrier
def MoveSignature.Clears (m : MoveSignature T)
    (C : Configuration V) (B : OrientedBranch T) : Prop :=
  ∀ v ∈ B.vertices, m.BalancesAt C v
def MoveSignature.boundaryFlux (m : MoveSignature T)
    (B : OrientedBranch T) : ℤ :=
  (m.count B.root B.parent : ℤ) -
    2 * (m.count B.parent B.root : ℤ)
def MoveSignature.CausalOutward (m : MoveSignature T)
    (B : OrientedBranch T) : Prop :=
  0 < m.count B.root B.parent
def MoveSignature.FeasibleClearing (m : MoveSignature T)
    (C : Configuration V) (B : OrientedBranch T) : Prop :=
  MoveSignature.SupportedOn m B ∧
    MoveSignature.Clears m C B ∧
    MoveSignature.CausalOutward m B
def MoveSignature.EmptyExcursion (m : MoveSignature T)
    (B : OrientedBranch T) : Prop :=
  MoveSignature.SupportedOn m B ∧
    ∀ v ∈ B.vertices,
      (m.incoming v : ℤ) - 2 * (m.outgoing v : ℤ) = 0
section LegalSequences
variable [DecidableEq V]
def BranchPebbleStep (B : OrientedBranch T)
    (C D : Configuration V) : Prop :=
  ∃ u v,
    T.graph.Adj u v ∧
    2 ≤ C u ∧
    u ∈ B.carrier ∧
    v ∈ B.carrier ∧
    D = move C u v
def BranchReach (B : OrientedBranch T)
    (C D : Configuration V) : Prop :=
  Relation.ReflTransGen B.BranchPebbleStep C D
def Cleared (B : OrientedBranch T) (D : Configuration V) : Prop :=
  ∀ v ∈ B.vertices, D v = 0
def withBoundary (B : OrientedBranch T) (C : Configuration V) (q : ℕ) :
    Configuration V :=
  Function.update C B.parent q
def IsChildVertex (B : OrientedBranch T) (v : V) : Prop :=
  T.graph.Adj B.root v ∧ v ≠ B.parent
def childOfVertex (B : OrientedBranch T) (v : V)
    (h : B.IsChildVertex v) : B.Child where
  vertex := v
  adj := h.1
  ne_parent := h.2
def IsOccupiedChildVertex
    (B : OrientedBranch T) (C : Configuration V) (v : V) : Prop :=
  ∃ h : B.IsChildVertex v,
    (B.childBranch (B.childOfVertex v h)).Occupied C
def OccupiedChild (B : OrientedBranch T) (C : Configuration V) :=
  {v : V // B.IsOccupiedChildVertex C v}
noncomputable instance OccupiedChild.instFintype
    (B : OrientedBranch T) (C : Configuration V) :
    Fintype (B.OccupiedChild C) :=
  Fintype.ofInjective
    (fun t : B.OccupiedChild C => (t.1 : V))
    Subtype.val_injective
noncomputable def OccupiedChild.child
    {B : OrientedBranch T} {C : Configuration V}
    (t : B.OccupiedChild C) : B.Child :=
  B.childOfVertex t.1 (Classical.choose t.2)
noncomputable def childMessageTerm
    (B : OrientedBranch T) (C : Configuration V) (v : V) : ℤ :=
  if h : B.IsChildVertex v then
    messageContribution
      (branchMessage C (B.childBranch (B.childOfVertex v h)))
  else
    0
noncomputable def OccupiedChild.gain
    {B : OrientedBranch T} {C : Configuration V}
    (t : B.OccupiedChild C) : ℤ :=
  messageContribution (branchMessage C (B.childBranch t.child))
noncomputable def occupiedChildTasks
    (B : OrientedBranch T) (C : Configuration V) :
    List (B.OccupiedChild C) := by
  classical
  exact (Finset.univ : Finset (B.OccupiedChild C)).toList
def ClearOutcome (B : OrientedBranch T) (C : Configuration V)
    (q : ℕ) (D : Configuration V) : Prop :=
  B.BranchReach (B.withBoundary C q) D ∧ B.Cleared D
noncomputable def carrierMass (B : OrientedBranch T) (C : Configuration V) : ℕ :=
  ∑ v ∈ B.carrier, C v
noncomputable def boundaryParityWeight (B : OrientedBranch T) (v : V) : ℤ :=
  if T.graph.dist B.parent v % 2 = 0 then 1 else -1
noncomputable def signedCarrierMass
    (B : OrientedBranch T) (C : Configuration V) : ℤ :=
  ∑ v ∈ B.carrier, B.boundaryParityWeight v * (C v : ℤ)
noncomputable def signatureChildFluxSum
    (m : MoveSignature T) (B : OrientedBranch T) : ℤ :=
  ∑ v : V,
    if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
      (m.count v B.root : ℤ) - 2 * (m.count B.root v : ℤ)
    else
      0
def ExactBoundaryInvariant (C : Configuration V) (B : OrientedBranch T) : Prop :=
  B.Occupied C →
    ∀ d : ℤ, branchMessage C B = some d →
      ∀ q : ℕ,
        (0 < (q : ℤ) + d →
          ∃ D : Configuration V,
            B.ClearOutcome C q D ∧
              (D B.parent : ℤ) = (q : ℤ) + d) ∧
        (∀ D : Configuration V,
          B.ClearOutcome C q D →
            (D B.parent : ℤ) ≤ (q : ℤ) + d) ∧
        ((q : ℤ) + d ≤ 0 →
          ¬ ∃ D : Configuration V,
            B.ClearOutcome C q D ∧ 0 < D B.parent)
end LegalSequences
end OrientedBranch
end TreeStack


