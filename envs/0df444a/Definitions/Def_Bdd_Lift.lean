-- Prove2me | Definitions.Def_Bdd_Lift
-- name    : Bdd_Lift
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:00:43.043804+00:00
-- url     : https://prove2.me/theorems/f94b7afb-c931-4070-a1db-89fc68b800c4
-- title:
--   Lift
-- statement:
--   Definitions and structural lemmas for Lift, from Eshel Yaron and contributors's pinned Correctness of binary decision diagrams for CNF formulas development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Lift.lean

import Definitions.Def_Bdd_Basic
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_Pointer_MayPrecede_node_terminal
import Theorems.Thm_Pointer_not_terminal_MayPrecede
attribute [local simp] Nary.restrict_const


set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered
namespace Lift
@[simp]
def lift (h : n ≤ n') (B : Bdd n m) : Bdd n' m :=
  ⟨ Vector.map
      (fun N ↦ ⟨⟨N.var.1, Fin.val_lt_of_le N.var h⟩, N.low, N.high⟩)
      B.heap,
    B.root
  ⟩
lemma lift_edge_iff {h : n ≤ n'} {B : Bdd n m} {p q : Pointer m} :
    Edge B.heap p q ↔ Edge (lift h B).heap p q := by
  constructor
  · intro e
    cases e with
    | low  _ => left;  simpa
    | high _ => right; simpa
  · intro e
    cases e with
    | low  _ => left;  simp_all
    | high _ => right; simp_all
lemma lift_reachable_iff {h : n ≤ n'} {B : Bdd n m} {p : Pointer m} :
    Pointer.Reachable B.heap B.root p ↔ Pointer.Reachable (lift h B).heap (lift h B).root p := by
  constructor
  · intro r
    induction r with
    | refl => left
    | tail _ e ih =>
      right
      · exact ih
      · exact (lift_edge_iff.mp e)
  · intro r
    induction r with
    | refl => left
    | tail _ e ih =>
      right
      · exact ih
      · exact (lift_edge_iff.mpr e)
lemma lift_preserves_MayPrecede {h : n ≤ n'} {B : Bdd n m} {p q : Pointer m} :
    Pointer.MayPrecede (lift h B).heap p q ↔ Pointer.MayPrecede B.heap p q := by
  constructor
  · intro hm
    cases p with
    | terminal _ =>
      absurd hm
      exact Pointer.not_terminal_MayPrecede
    | node j =>
      cases q with
      | terminal _ =>
        apply Pointer.MayPrecede_node_terminal
      | node j' =>
        simp only [Pointer.MayPrecede, Nat.succ_eq_add_one, Pointer.toVar, lift, Fin.getElem_fin,
          Vector.getElem_map, Fin.mk_lt_mk, Fin.val_fin_lt] at hm
        simp only [Pointer.MayPrecede, Nat.succ_eq_add_one]
        aesop
  · intro hm
    cases p with
    | terminal _ =>
      absurd hm
      exact Pointer.not_terminal_MayPrecede
    | node j =>
      cases q with
      | terminal _ =>
        apply Pointer.MayPrecede_node_terminal
      | node j' =>
        simp only [Pointer.MayPrecede, Nat.succ_eq_add_one] at hm
        simp only [Pointer.MayPrecede, Nat.succ_eq_add_one, lift]
        simp_all [Vector.getElem_map, Pointer.toVar]
lemma lift_preserves_RelevantEdge {h : n ≤ n'} {B : Bdd n m} {p q : Pointer m} :
    ( ∃ (hp : Pointer.Reachable (lift h B).heap (lift h B).root p)
        (hq : Pointer.Reachable (lift h B).heap (lift h B).root q), Bdd.RelevantEdge (lift h B) ⟨p, hp⟩ ⟨q, hq⟩) ↔
    ( ∃ (hp : Pointer.Reachable B.heap B.root p)
        (hq : Pointer.Reachable B.heap B.root q), Bdd.RelevantEdge B ⟨p, hp⟩ ⟨q, hq⟩) := by
  constructor
  · rintro ⟨hp, hq, hr⟩
    use (lift_reachable_iff.mpr hp)
    use (lift_reachable_iff.mpr hq)
    cases hr with
    | low  hl => simp at hl; left ; assumption
    | high hh => simp at hh; right; assumption
  · rintro ⟨hp, hq, hr⟩
    use (lift_reachable_iff.mp hp)
    use (lift_reachable_iff.mp hq)
    cases hr with
    | low  hl => simp at hl; left ; simpa
    | high hh => simp at hh; right; simpa
lemma lift_ordered {h : n ≤ n'} {B : Bdd n m} : B.Ordered → (lift h B).Ordered := by
  rintro ho ⟨x, hx⟩ ⟨y, hy⟩ e
  apply lift_preserves_MayPrecede.mpr
  exact ho (lift_preserves_RelevantEdge.mp ⟨hx, hy, e⟩).2.2
def olift (h : n ≤ n') (O : OBdd n m) : OBdd n' m := ⟨(lift h O.1), lift_ordered O.2⟩
attribute [local implicit_reducible] olift
@[simp]
lemma olift_trivial_eq {h : n = n'} {O : OBdd n m} : (olift (n' := n') (by rw [h]) O) = h ▸ O := by
  rcases O with ⟨⟨M, r⟩, o⟩
  simp only [olift, lift]
  congr
  · subst h
    simp only
    rcases M with ⟨V, l⟩
    simp [Vector.map, id_eq]
  · subst h
    simp
@[simp]
lemma olift_preserves_root {h : n ≤ n'} {O : OBdd n m} : (olift h O).1.root = O.1.root := by simp [olift]
end Lift


