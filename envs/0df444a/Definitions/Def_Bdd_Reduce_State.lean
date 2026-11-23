-- Prove2me | Definitions.Def_Bdd_Reduce_State
-- name    : Bdd_Reduce_State
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T06:55:38.805826+00:00
-- url     : https://prove2.me/theorems/1df0c1c2-e65d-4331-8c0f-4162080d81c2
-- title:
--   State
-- statement:
--   Definitions and structural lemmas for State, from Eshel Yaron and contributors's pinned Correctness of binary decision diagrams for CNF formulas development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const


set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
namespace Reduce
instance : LinearOrder RawPointer := inferInstanceAs (LinearOrder (Bool ⊕ₗ Nat))
def leKeyPair (a b : RawPointer × RawPointer) : Bool :=
  if a.1 = b.1 then decide (a.2 ≤ b.2) else decide (a.1 ≤ b.1)
def KeyLE (a b : RawPointer × RawPointer) : Prop := leKeyPair a b = true
structure State (n) (m) where
  size : Nat
  heap : Vector (RawNode n) size
  ids  : Vector (Option RawPointer) m
structure ProvedState (n m : Nat) where
  state : State n m
  hh    : ∀ k : Fin state.size, state.heap[k].Bounded k
def initial (n m : Nat) : State n m :=
  ⟨0, Vector.emptyWithCapacity 0, Vector.replicate m none⟩
def provedStateInitial (n m : Nat) : ProvedState n m where
  state := ⟨0, Vector.emptyWithCapacity 0, Vector.replicate m none⟩
  hh := fun k => k.elim0
def get_id {n m : Nat} (ps : ProvedState n m) (p : Pointer m)
    (h : ∀ j, p = .node j → (ps.state.ids[j]).isSome) : RawPointer :=
  match p with
  | .terminal b => .inl b
  | .node j     => (ps.state.ids[j]).get (h j rfl)
def set_id {n m : Nat} (ps : ProvedState n m) (j : Fin m) (p : RawPointer) : ProvedState n m :=
  { state := { size := ps.state.size, heap := ps.state.heap, ids := ps.state.ids.set j (some p) },
    hh    := ps.hh }
def push_node {n m : Nat} (ps : ProvedState n m) (N : RawNode n)
    (hN : N.Bounded ps.state.size) : ProvedState n m × RawPointer :=
  let hh' : ∀ k : Fin (ps.state.size + 1), (ps.state.heap.push N)[k].Bounded k := fun k => by
    by_cases hlt : k.1 < ps.state.size
    · simp only [Fin.getElem_fin, Vector.getElem_push_lt hlt]
      exact ps.hh ⟨k.1, hlt⟩
    · have hk : k.1 = ps.state.size := by omega
      simp only [Fin.getElem_fin, show k.1 = ps.state.size from hk,
                 Vector.getElem_push_eq]
      exact hN
  ⟨⟨{ size := ps.state.size + 1, heap := ps.state.heap.push N, ids := ps.state.ids }, hh'⟩,
   .inr ps.state.size⟩
def Invariant {n m : Nat} (O : OBdd n m) (ps : ProvedState n m) (i : Nat) : Prop :=
  -- Completeness
  (∀ (j : Fin m),
      i < O.1.heap[j].var.1 →
      Reachable O.1.heap O.1.root (.node j) →
      (ps.state.ids[j]).isSome) ∧
  -- Correctness
  ∀ (j : Fin m) (ptr : RawPointer),
      ps.state.ids[j] = some ptr →
      ∃ hj   : Bdd.Ordered ⟨O.1.heap, .node j⟩,
        ∃ hptr : ptr.Bounded ps.state.size,
          ∃ ho : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, ptr.cook hptr⟩,
            OBdd.Reduced ⟨⟨cook_heap ps.state.heap ps.hh, ptr.cook hptr⟩, ho⟩ ∧
            ∀ I,
              OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, ptr.cook hptr⟩, ho⟩ I =
              OBdd.evaluate ⟨⟨O.1.heap, .node j⟩, hj⟩ I
def VarInvariant {n m : Nat} (O : OBdd n m) (ps : ProvedState n m) : Prop :=
  ∀ (j : Fin m) (k : Fin ps.state.size),
    ps.state.ids[j] = some (.inr k.1) →
    O.1.heap[j].var.1 ≤ ps.state.heap[k].va.1
def AllAbove {n m : Nat} (ps : ProvedState n m) (i : Nat) : Prop :=
  ∀ k : Fin ps.state.size, i < ps.state.heap[k].va.1
def HeapInjective {n : Nat} (ps : ProvedState n m) : Prop :=
  ∀ k1 k2 : Fin ps.state.size, ps.state.heap[k1] = ps.state.heap[k2] → k1 = k2
def EntryCorrect {n m : Nat} (O : OBdd n m) (ps : ProvedState n m) (i : Nat)
    (entry : (RawPointer × RawPointer) × Fin m) : Prop :=
  Reachable O.1.heap O.1.root (.node entry.2) ∧
  O.1.heap[entry.2].var.1 = i ∧
  (∀ l, O.1.heap[entry.2].low = .node l → ps.state.ids[l] = some entry.1.1) ∧
  (∀ l, O.1.heap[entry.2].high = .node l → ps.state.ids[l] = some entry.1.2) ∧
  (∀ b, O.1.heap[entry.2].low = .terminal b → entry.1.1 = .inl b) ∧
  (∀ b, O.1.heap[entry.2].high = .terminal b → entry.1.2 = .inl b)
abbrev NodePushedCorrectly {n m : Nat} (O : OBdd n m) (ps : ProvedState n m)
    (entry : (RawPointer × RawPointer) × Fin m)
    (hbound : entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size) : Prop :=
  let N    : RawNode n := ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩
  let hN   : N.Bounded ps.state.size := ⟨hbound.1, hbound.2⟩
  let ps₁  := (push_node ps N hN).1
  let ptr  := (push_node ps N hN).2
  let ps₂  := set_id ps₁ entry.2 ptr
  ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
  ∃ hp : ptr.Bounded ps₂.state.size,
  ∃ ho : Bdd.Ordered ⟨cook_heap ps₂.state.heap ps₂.hh, ptr.cook hp⟩,
    OBdd.Reduced ⟨⟨cook_heap ps₂.state.heap ps₂.hh, ptr.cook hp⟩, ho⟩ ∧
    ∀ I, OBdd.evaluate ⟨⟨cook_heap ps₂.state.heap ps₂.hh, ptr.cook hp⟩, ho⟩ I =
         OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I
abbrev CurptrSemantic {n m : Nat} (O : OBdd n m) (ps : ProvedState n m)
    (curptr : RawPointer) (entry : (RawPointer × RawPointer) × Fin m) : Prop :=
  ∃ hj : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
  ∃ hp : curptr.Bounded ps.state.size,
  ∃ ho : Bdd.Ordered ⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩,
    OBdd.Reduced ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ ∧
    ∀ I, OBdd.evaluate ⟨⟨cook_heap ps.state.heap ps.hh, curptr.cook hp⟩, ho⟩ I =
         OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I
end Reduce


