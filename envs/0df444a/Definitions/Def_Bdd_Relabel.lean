-- Prove2me | Definitions.Def_Bdd_Relabel
-- name    : Bdd_Relabel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:00:45.182861+00:00
-- url     : https://prove2.me/theorems/6d2fe63b-789c-4dc6-bf29-1dbacba7cdb8
-- title:
--   Relabel
-- statement:
--   Definitions and structural lemmas for Relabel, from Eshel Yaron and contributors's pinned Correctness of binary decision diagrams for CNF formulas development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Relabel.lean

import Definitions.Def_Bdd_Basic
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_P2M_OBdd_evaluate_node___75814e9183f4
import Theorems.Thm_P2M_OBdd_evaluate_terminal__321343d95937
import Theorems.Thm_Pointer_MayPrecede_node_terminal
import Theorems.Thm_Pointer_not_terminal_MayPrecede
attribute [local simp] Nary.restrict_const


set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered Bdd.RelevantMayPrecede
namespace Relabel
def relabel_node {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n) : Node n m → Node (f n) m
  | ⟨var, low, high⟩ => ⟨⟨f var.1, hf _⟩, low, high⟩
def relabel_heap {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n) :
    Vector (Node n m) m → Vector (Node (f n) m) m := Vector.map (relabel_node hf)
def relabel {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n) : Bdd n m → Bdd (f n) m
  | ⟨heap, root⟩ => ⟨relabel_heap hf heap, root⟩
attribute [local implicit_reducible] relabel relabel_heap relabel_node
lemma relabel_edge_iff {B : Bdd n m} {x y : Pointer m} {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n} :
    Edge B.heap x y ↔ Edge (relabel hf B).heap x y := by
  constructor
  · intro e
    cases e with
    | low  _ => left;  simpa +instances [relabel, relabel_heap]
    | high _ => right; simpa +instances [relabel, relabel_heap]
  · intro e
    cases e with
    | low  _ => left;  simp_all +instances [relabel, relabel_heap, relabel_node]
    | high _ => right; simp_all +instances [relabel, relabel_heap, relabel_node]
lemma relabel_reachable_iff {B : Bdd n m} : Pointer.Reachable B.heap B.root x ↔ Pointer.Reachable (relabel h B).heap (relabel h B).root x := by
  constructor
  · intro r
    induction r with
    | refl => left
    | tail _ e ih =>
      right
      · exact ih
      · exact (relabel_edge_iff.mp e)
  · intro r
    induction r with
    | refl => left
    | tail _ e ih =>
      right
      · exact ih
      · exact (relabel_edge_iff.mpr e)
lemma relabel_relevantMayPrecede {B : Bdd n m} {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n}
    {hu : ∀ i i' : Fin n, i < i' → B.usesVar i → B.usesVar i' → f i < f i'}
    {x y : Pointer m}
    {hx : Pointer.Reachable (relabel hf B).heap (relabel hf B).root x}
    {hy : Pointer.Reachable (relabel hf B).heap (relabel hf B).root y} :
    B.RelevantMayPrecede ⟨x, relabel_reachable_iff.mpr hx⟩ ⟨y, relabel_reachable_iff.mpr hy⟩ → (relabel hf B).RelevantMayPrecede ⟨x, hx⟩ ⟨y, hy⟩ := by
  intro h
  simp +instances only [Bdd.RelevantMayPrecede] at h
  simp +instances only [Bdd.RelevantMayPrecede]
  cases x with
  | terminal _ => absurd h; exact Pointer.not_terminal_MayPrecede
  | node j =>
    cases y with
    | terminal _ => apply Pointer.MayPrecede_node_terminal
    | node j' =>
      simp +instances only [Pointer.MayPrecede, Pointer.toVar, Nat.succ_eq_add_one, Fin.getElem_fin] at h
      simp +instances only [Pointer.MayPrecede, relabel, relabel_heap, Pointer.toVar]
      simp +instances only [Nat.succ_eq_add_one, Fin.getElem_fin, Vector.getElem_map]
      simp +instances only [relabel_node, Fin.eta, Fin.mk_lt_mk]
      apply hu
      · exact h
      · use j
        constructor
        · exact relabel_reachable_iff.mpr hx
        · rfl
      · use j'
        constructor
        · exact relabel_reachable_iff.mpr hy
        · rfl
lemma relabel_relevantEdge {B : Bdd n m} {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n}
    {x y : Pointer m}
    {hx : Pointer.Reachable (relabel hf B).heap (relabel hf B).root x}
    {hy : Pointer.Reachable (relabel hf B).heap (relabel hf B).root y} :
    (relabel hf B).RelevantEdge ⟨x, hx⟩ ⟨y, hy⟩ → B.RelevantEdge ⟨x, relabel_reachable_iff.mpr hx⟩ ⟨y, relabel_reachable_iff.mpr hy⟩ := by
  intro h
  simp_all +instances only [Bdd.RelevantEdge, relabel, relabel_heap]
  cases h with
  | low _ =>
    left
    simp_all +instances [relabel_node]
  | high _ =>
    right
    simp_all +instances [relabel_node]
lemma relabel_ordered {B : Bdd n m} {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n} :
    (∀ i i' : Fin n, i < i' → B.usesVar i → B.usesVar i' → f i < f i') → Bdd.Ordered B → Bdd.Ordered (relabel hf B) := by
  intro hu ho _ _ hxy
  apply relabel_relevantMayPrecede
  exact hu
  apply ho
  exact relabel_relevantEdge hxy
def orelabel (O : OBdd n m) {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n)
    (hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i') : OBdd (f n) m :=
    ⟨(relabel hf O.1), relabel_ordered hu O.2⟩
attribute [local implicit_reducible] orelabel
lemma orelabel_low {O : OBdd n m} {h : O.1.root = .node j} {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n)
    (hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i') :
    (OBdd.low (orelabel O hf hu) h) = orelabel (O.low h) hf (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_low_usesVar hi) (OBdd.usesVar_of_low_usesVar hi')) := by
  rcases O with ⟨B, o⟩
  simp +instances only [OBdd.low]
  congr
  simp +instances only [orelabel, relabel, relabel_heap, Bdd.low_heap_eq_heap]
  simp +instances only at h
  simp_rw [h]
  simp +instances only [Bdd.low]
  congr 1
  simp_all +instances only [Fin.getElem_fin, Vector.getElem_map]
  rfl
lemma orelabel_high {O : OBdd n m} {h : O.1.root = .node j} {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n)
    (hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i') :
    (OBdd.high (orelabel O hf hu) h) = orelabel (O.high h) hf (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_high_usesVar hi) (OBdd.usesVar_of_high_usesVar hi')) := by
  rcases O with ⟨B, o⟩
  simp +instances only [OBdd.high]
  congr
  simp +instances only [orelabel, relabel, relabel_heap, Bdd.high_heap_eq_heap]
  simp +instances only at h
  simp_rw [h]
  simp +instances only [Bdd.high]
  congr 1
  simp_all +instances only [Fin.getElem_fin, Vector.getElem_map]
  rfl
@[simp]
theorem orelabel_evaluate (O : OBdd n m) {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n}
    {hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i'} {I : Vector Bool (f n)} :
    OBdd.evaluate (orelabel O hf hu) I = O.evaluate (Vector.ofFn (fun i ↦ I[f i]'(hf i))) := by
  simp +instances only [orelabel]
  cases O_root_def : O.1.root with
  | terminal _ =>
    simp +instances only [relabel]
    rw [OBdd.evaluate_terminal' O_root_def]
    simp_rw [O_root_def]
    rw [OBdd.evaluate_terminal]
    simp
  | node j =>
    rw [OBdd.evaluate_node'' O_root_def]
    have that : (⟨(relabel hf O.1), relabel_ordered hu O.2⟩ : OBdd _ _).1.root = Pointer.node j := O_root_def
    rw [OBdd.evaluate_node'' that]
    simp +instances only
    congr 1
    · simp +instances only [eq_iff_iff, Bool.coe_iff_coe]
      simp +instances only [relabel, relabel_heap, Fin.getElem_fin, Vector.getElem_map, relabel_node]
      exact Eq.symm (Vector.getElem_ofFn ..)
    · have := orelabel_evaluate
        (hu := (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_high_usesVar hi) (OBdd.usesVar_of_high_usesVar hi')))
        (hf := hf)
        (O.high O_root_def) (I := I)
      rw [← this]
      rw [← orelabel_high hf hu]
      rfl
    · have := orelabel_evaluate
        (hu := (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_low_usesVar hi) (OBdd.usesVar_of_low_usesVar hi')))
        (hf := hf)
        (O.low O_root_def) (I := I)
      rw [← this]
      rw [← orelabel_low hf hu]
      rfl
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
@[simp]
lemma relabel_id {B : Bdd n m} : relabel (f := id) (by simp) B = B := by
  simp +instances only [id_eq, relabel, relabel_heap]
  congr
  ext i hi
  simp +instances only [Vector.getElem_map, relabel_node, id_eq, Fin.eta]
end Relabel


