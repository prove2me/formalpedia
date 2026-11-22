-- Prove2me | Definitions.Def_LeanPool_Parikh_Activation
-- name    : LeanPool_Parikh_Activation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T09:49:25.534835+00:00
-- url     : https://prove2.me/theorems/900aed7b-a6e9-49b3-805e-a0955425f5ff
-- title:
--   Activation
-- statement:
--   Definitions and structural lemmas for Activation, from Umang Mathur; LeanPool contributors's pinned Parikh's theorem and a certified semilinear grammar compiler development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Activation.lean

module
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Algebra.Order.Group.Nat
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace Parikh
@[expose] def ActivationOrder {N C : Type*} (required : C → N) (added : C → Set N) :
    Set N → List C → Prop
  | _, [] => True
  | U, c :: cs => required c ∈ U ∧ ActivationOrder required added (U ∪ added c) cs
@[expose] def Activatable {N C : Type*} (required : C → N) (added : C → Set N)
    (U : Set N) (D : Finset C) : Prop :=
  ∃ order : List C, order.Nodup ∧ (∀ c, c ∈ order ↔ c ∈ D) ∧
    ActivationOrder required added U order
namespace ActivationOrder
variable {N C : Type*} {required : C → N} {added : C → Set N}
end ActivationOrder
structure ActivationTest (N C : Type*) [DecidableEq N] [DecidableEq C] where
  /-- Decide whether all operations can be activated from the initial support. -/
  run : (C → N) → (C → Finset N) → Finset N → Finset C → Bool
  correct : ∀ required added U D,
    run required added U D = true ↔
      Activatable required (fun c => (added c : Set N)) (U : Set N) D
@[expose] def ContextsActivatable {T : Type*} (g : ContextFreeGrammar T)
    (B : ParseTree T g.NT) (D : Finset (ParseTree T g.NT)) : Prop :=
  ∃ order : List (ParseTree T g.NT), order.Nodup ∧
    (∀ C, C ∈ order ↔ C ∈ D) ∧
    ∃ roots : ParseTree T g.NT → g.NT,
      (∀ C ∈ D, Cycle g C (roots C)) ∧
      ActivationOrder roots ParseTree.support B.support order
@[expose] noncomputable def contextComponent {T : Type*} [DecidableEq T]
    (B : ParseTree T N) (D : Finset (ParseTree T N)) : Component T := by
  classical
  exact ⟨B.weight + ∑ C ∈ D, C.weight, D.toList.map ParseTree.weight⟩
@[expose] def treeRepresentation {T : Type*} [DecidableEq T] (g : ContextFreeGrammar T) :
    Set (Vector T) :=
  {v | ∃ B D, IsBase g B ∧ (∀ C ∈ D, IsBoundedCycle g C) ∧
    ContextsActivatable g B D ∧ v ∈ (contextComponent B D).denotation}
end Parikh


