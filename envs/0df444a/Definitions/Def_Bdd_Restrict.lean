-- Prove2me | Definitions.Def_Bdd_Restrict
-- name    : Bdd_Restrict
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:08:50.853986+00:00
-- url     : https://prove2.me/theorems/c4516c7c-9f03-422f-a73d-946dfcc61f9b
-- title:
--   Restrict
-- statement:
--   Definitions and structural lemmas for Restrict, from Eshel Yaron and contributors's pinned Correctness of binary decision diagrams for CNF formulas development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Restrict.lean

import Definitions.Def_Bdd_Basic
import Std.Data.HashMap.Lemmas
import Theorems.Thm_Bdd_ordered_of_low_high_ordered
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_Nary_restrict_if
import Theorems.Thm_OBdd_evaluate_eq_evaluate_of_ordered_heap_all_reachable_eq
import Theorems.Thm_OBdd_not_oedge_reachable
import Theorems.Thm_OBdd_var_lt_high_var
import Theorems.Thm_OBdd_var_lt_low_var
import Theorems.Thm_P2M_OBdd_evaluate_node__1867d6ba89de
import Theorems.Thm_P2M_OBdd_evaluate_node___75814e9183f4
import Theorems.Thm_RawBdd_RawNode_cook_equiv
import Theorems.Thm_RawBdd_RawPointer_cook_equiv
import Theorems.Thm_RawBdd_cook_high
import Theorems.Thm_RawBdd_cook_low
import Theorems.Thm_RawBdd_push_evaluate
import Theorems.Thm_RawBdd_push_ordered
attribute [local simp] Nary.restrict_const


set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered RawBdd.RawPointer RawBdd.RawPointer.Bounded
namespace Restrict
open RawBdd
structure State (n) (m) where
  size : Nat
  heap : Vector (RawNode n) size
  cache : Std.HashMap (Pointer m) RawPointer
def initial : State n m := ⟨_, (Vector.emptyWithCapacity 0), Std.HashMap.emptyWithCapacity 0⟩
def Invariant (b : Bool) (i : Fin n) (O : OBdd n m) (s : State n m) :=
  ∃ hh : (∀ i : Fin s.size, RawNode.Bounded i s.heap[i]),
    ∀ (k : (Pointer m)) (p : RawPointer),
      s.cache[k]? = some p →
      (∀ j h, p = .inr j → (if (Pointer.toVar O.1.heap k).1 = i.1 then (s.heap[j]'h).va.1 > (Pointer.toVar O.1.heap k) else (s.heap[j]'h).va.1 = (Pointer.toVar O.1.heap k))) ∧
      ∃ hk1 : Bdd.Ordered ⟨O.1.heap, k⟩,
          ∃ hp : p.Bounded s.size,
            ∃ o : Bdd.Ordered ⟨cook_heap s.heap hh, p.cook hp⟩,
                OBdd.evaluate ⟨⟨cook_heap s.heap hh, p.cook hp⟩, o⟩ = Nary.restrict (OBdd.evaluate ⟨⟨O.1.heap, k⟩, hk1⟩) b i
attribute [local implicit_reducible] Invariant
lemma inv_initial {b} {i} {O : OBdd n m} : Invariant b i O initial := by
  constructor
  · intro k p hp
    simp only [initial, Std.HashMap.getElem?_emptyWithCapacity, reduceCtorEq] at hp
  · rintro ⟨_, c⟩
    simp only [initial, not_lt_zero] at c
lemma heap_push_aux (s : State n m) (inv : Invariant b i O s)
    (hNl : ∃ k : Pointer m, s.cache[k]? = some N.lo)
    (hNh : ∃ k : Pointer m, s.cache[k]? = some N.hi)
    (hNv : (if (O.1.root.toVar O.1.heap).1 = i.1 then N.va.1 > (O.1.root.toVar O.1.heap).1 else N.va.1 = (O.1.root.toVar O.1.heap).1))
    (hxl : ∀ j h (_ : N.lo = .inr j), N.va.1 < (s.heap[j]'h).va.1)
    (hxh : ∀ j h (_ : N.hi = .inr j), N.va.1 < (s.heap[j]'h).va.1)
    (hh : ∀ h0 (h1 : Bdd.Ordered _),
      OBdd.evaluate ⟨⟨cook_heap (s.heap.push N) h0, .node ⟨s.size, by simp⟩⟩, h1⟩ = Nary.restrict (O.evaluate) b i) :
    Invariant b i O
      { size := s.size + 1, heap := s.heap.push N, cache := s.cache.insert (O.1.root) (Sum.inr s.size) } := by
  rcases hNl with ⟨kl, hkl⟩
  rcases hNh with ⟨kh, hkh⟩
  have hN : RawNode.Bounded s.size N := by
    simp only [RawNode.Bounded]
    constructor
    · exact (inv.2 kl N.lo hkl).2.2.1
    · exact (inv.2 kh N.hi hkh).2.2.1
  have : ∀ (i : Fin (s.size + 1)), RawNode.Bounded (↑i) (s.heap.push N)[i] := by
    intro i
    simp only [Fin.getElem_fin]
    rw [Vector.getElem_push]
    split
    next hi => exact inv.1 ⟨i.1, hi⟩
    next hi =>
      have : i.1 = s.size := by omega
      rw [this]
      exact hN
  use this
  intro k p
  simp only
  intro hp
  rw [Std.HashMap.getElem?_insert] at hp
  simp only [beq_iff_eq] at hp
  split at hp
  next heq =>
    subst heq
    constructor
    · intro j hs hj
      rw [Vector.getElem_push]
      split
      next heqq =>
        injection hp with hpp
        rw [hj] at hpp
        injection hpp with hppp
        split
        next contra => rw [hppp] at contra; absurd contra; simp only [lt_self_iff_false,
          not_false_eq_true]
        next =>
          split at hNv
          next contra => simp_all
          next contra => contradiction
      next heqq =>
        split
        next contra => injection hp with hi; subst hi; injection hj with hi; rw [hi] at contra; absurd contra; simp only [lt_self_iff_false,
          not_false_eq_true]
        next =>
          split at hNv
          next => simp_all
          next contra => rw [← hNv]
    use O.2
    injection hp with hpe
    subst hpe
    have hb : RawPointer.Bounded (s.size + 1) (Sum.inr s.size) := by intro i hi; injection hi with hie; subst hie; simp
    use hb
    have hoo : Bdd.Ordered ⟨cook_heap (s.heap.push N) this, RawPointer.cook (Sum.inr s.size) hb⟩ := by
      apply Bdd.ordered_of_low_high_ordered rfl
      · simp only [Bdd.low, cook_heap]
        simp only [Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_push_eq]
        rw [← cook_low]
        swap; apply RawPointer.bounded_of_le (inv.2 kl N.lo hkl).2.2.1; simp only [le_add_iff_nonneg_right, zero_le]
        rcases (inv.2 kl N.lo hkl).2.2.2 with that
        apply push_ordered
        · exact this
        · exact that.1
      ·
        simp [Nat.succ_eq_add_one, Bdd.var, cook_heap, Bdd.low, RawPointer.cook]
        cases heq : N.lo with
        | inl val =>
          rw [← cook_low]
          simp_rw [heq]
          simp only [RawPointer.cook, Pointer.toVar_terminal_eq, Nat.succ_eq_add_one]
          simp only [Pointer.toVar, Nat.succ_eq_add_one, Fin.getElem_fin, Vector.getElem_ofFn,
            Vector.getElem_push_eq, Fin.mk_lt_mk, Fin.is_lt]
          apply RawPointer.bounded_of_le (inv.2 kl N.lo hkl).2.2.1; simp only [le_add_iff_nonneg_right, zero_le]
        | inr val =>
          have hvs : val < s.size := by
            apply RawPointer.bounded_of_le (inv.2 kl N.lo hkl).2.2.1 .refl heq
          rw [← cook_low]
          simp_rw [heq]
          simp only [RawNode.cook, RawPointer.cook]
          simp only [Pointer.toVar, Nat.succ_eq_add_one, Fin.getElem_fin, Vector.getElem_ofFn,
            Vector.getElem_push_eq, Fin.mk_lt_mk, Fin.val_fin_lt, gt_iff_lt]
          rw [Vector.getElem_push_lt]
          have hvs : val < s.size := by
            apply RawPointer.bounded_of_le (inv.2 kl N.lo hkl).2.2.1 .refl heq
          exact hxl _ hvs heq
          exact hvs
          apply RawPointer.bounded_of_le (inv.2 kl N.lo hkl).2.2.1; simp only [le_add_iff_nonneg_right, zero_le]
      · simp only [Bdd.high, cook_heap]
        simp only [Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_push_eq]
        rw [← cook_high]
        swap; apply RawPointer.bounded_of_le (inv.2 kh N.hi hkh).2.2.1; simp only [le_add_iff_nonneg_right, zero_le]
        rcases (inv.2 kh N.hi hkh).2.2.2 with that
        apply push_ordered
        · exact this
        · exact that.1
      ·
        simp [Nat.succ_eq_add_one, Bdd.var, cook_heap, Bdd.high, RawPointer.cook]
        cases heq : N.hi with
        | inl val =>
          rw [← cook_high]
          simp_rw [heq]
          simp only [RawPointer.cook, Pointer.toVar_terminal_eq, Nat.succ_eq_add_one]
          simp only [Pointer.toVar, Nat.succ_eq_add_one, Fin.getElem_fin, Vector.getElem_ofFn,
            Vector.getElem_push_eq, Fin.mk_lt_mk, Fin.is_lt]
          apply RawPointer.bounded_of_le (inv.2 kh N.hi hkh).2.2.1; simp only [le_add_iff_nonneg_right, zero_le]
        | inr val =>
          have hvs : val < s.size := by
            apply RawPointer.bounded_of_le (inv.2 _ _ hkh).2.2.1 .refl heq
          rw [← cook_high]
          simp_rw [heq]
          simp only [RawNode.cook, RawPointer.cook]
          simp only [Pointer.toVar, Nat.succ_eq_add_one, Fin.getElem_fin, Vector.getElem_ofFn,
            Vector.getElem_push_eq, Fin.mk_lt_mk, Fin.val_fin_lt, gt_iff_lt]
          rw [Vector.getElem_push_lt]
          exact hxh _ hvs heq
          apply RawPointer.bounded_of_le (inv.2 kh N.hi hkh).2.2.1; simp only [le_add_iff_nonneg_right, zero_le]
    use hoo
    generalize_proofs at *
    rw [show ⟨{ heap := O.1.heap, root := O.1.root }, _⟩ =  O by rfl]
    simp [RawPointer.cook]
    simp [RawPointer.cook] at hoo
    have := hh _ (by exact hoo)
    exact hh _ hoo
  next heq =>
    constructor
    · intro j hs hj
      rw [hj] at hp
      rcases (inv.2 k _ hp) with ⟨inv1, inv2⟩
      have := inv1 j (inv2.2.1 rfl) rfl
      rw [Vector.getElem_push_lt (inv2.2.1 rfl)]
      exact this
    rcases (inv.2 k p hp) with that
    use that.2.1
    have hb : ∀ {i}, p = Sum.inr i → i < s.size + 1 :=
      RawPointer.bounded_of_le that.2.2.1 (by simp only [le_add_iff_nonneg_right, zero_le])
    use hb
    have ho : Bdd.Ordered { heap := cook_heap (s.heap.push N) this, root := p.cook hb } := push_ordered that.2.2.2.1
    use ho
    ext I
    calc _
      _ = OBdd.evaluate ⟨{ heap := cook_heap (s.heap) inv.1, root := p.cook that.2.2.1 }, that.2.2.2.1⟩ I := by
        rw [OBdd.evaluate_eq_evaluate_of_ordered_heap_all_reachable_eq]
        · simp only [Fin.getElem_fin]
          intro j hj
          use (by omega)
          simp [cook_heap]
          exact RawNode.cook_equiv
        · simp only [RawPointer.cook_equiv]
    rw [that.2.2.2.2]
def heap_push (N : RawNode n) (s : (State n m)) (inv : Invariant b i O s)
    (hNl : ∃ k : Pointer m, s.cache[k]? = some N.lo)
    (hNh : ∃ k : Pointer m, s.cache[k]? = some N.hi)
    (hNv : (if (O.1.root.toVar O.1.heap).1 = i.1 then N.va.1 > (O.1.root.toVar O.1.heap).1 else N.va.1 = (O.1.root.toVar O.1.heap).1))
    (hxl : ∀ j h (_ : N.lo = .inr j), N.va.1 < (s.heap[j]'h).va.1)
    (hxh : ∀ j h (_ : N.hi = .inr j), N.va.1 < (s.heap[j]'h).va.1)
    (hh : ∀ h0 (h1 : Bdd.Ordered _),
      OBdd.evaluate ⟨⟨cook_heap (s.heap.push N) h0, .node ⟨s.size, by simp⟩⟩, h1⟩ = Nary.restrict (O.evaluate) b i)
    (hc : s.cache[O.1.root]? = none) :
    { r : State n m × RawPointer //
      (Invariant b i O r.1) ∧
      (r.1.cache[O.1.root]? = some r.2) ∧
      s.size ≤ r.1.size ∧
      (∀ (k : Pointer m),
        (∀ p, s.cache[k]? = some p → r.1.cache[k]? = some p) ∧
        (r.1.cache[k]? = none → s.cache[k]? = none) ∧
        (s.cache[k]? = none → (∃ p, r.1.cache[k]? = some p) → Pointer.Reachable O.1.heap O.1.root k))
    } :=
  ⟨⟨⟨s.size + 1, s.heap.push N, s.cache.insert O.1.root (.inr s.size)⟩, .inr s.size⟩, by
    constructor
    · exact heap_push_aux s inv hNl hNh hNv hxl hxh hh
    · constructor
      · simp only [Std.HashMap.getElem?_insert_self]
      · constructor
        · simp only [le_add_iff_nonneg_right, zero_le]
        · intro k
          constructor
          · intro p hkp
            rw [← hkp]
            simp only [Std.HashMap.getElem?_insert, beq_iff_eq, ite_eq_right_iff]
            intro contra
            rw [← contra] at hkp
            rw [hkp] at hc
            contradiction
          · constructor
            · simp only [getElem?_eq_none_iff, Std.HashMap.mem_insert, beq_iff_eq, not_or,
                and_imp, imp_self, implies_true]
            · rintro hk ⟨q, hq⟩
              simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at hq
              split at hq
              next heqq => subst heqq; constructor
              next heqq => rw [hk] at hq; contradiction
  ⟩
lemma insert_terminal_invariant (s0 : State n m) (inv : Invariant b i O s0) (ho : O.1.root = .terminal b') :
    Invariant b i O { size := s0.size, heap := s0.heap, cache := s0.cache.insert O.1.root (Sum.inl b') } := by
  constructor
  intro k p hp
  simp only at hp
  simp only
  rw [Std.HashMap.getElem?_insert] at hp
  simp only [beq_iff_eq] at hp
  split at hp
  next heq =>
    rw [← heq]
    constructor
    · intro j hj hjp
      subst hjp
      injection hp with hpp
      contradiction
    use O.2
    injection hp with hpe
    subst hpe
    use (fun contra ↦ by contradiction)
    simp [RawPointer.cook, ho, Bdd.Ordered_of_terminal]
  next =>
    constructor
    · exact (inv.2 _ _ hp).1
    exact (inv.2 _ _ hp).2
def restrict_helper (O : OBdd n m) (b : Bool) (i : Fin n) (s0 : State n m) (inv : Invariant b i O s0) :
    { r : State n m × RawPointer //
      (Invariant b i O r.1) ∧
      (r.1.cache[O.1.root]? = some r.2) ∧
      (s0.size ≤ r.1.size) ∧
      (∀ (k : Pointer m),
        (∀ p, s0.cache[k]? = some p → r.1.cache[k]? = some p) ∧
        (r.1.cache[k]? = none → s0.cache[k]? = none) ∧
        (s0.cache[k]? = none → (∃ p, r.1.cache[k]? = some p) → Pointer.Reachable O.1.heap O.1.root k))
    } :=
  match hc : s0.cache[O.1.root]? with
  | some root =>
    ⟨ ⟨s0, root⟩, ⟨inv, hc, .refl,
      by
        intro k
        constructor
        · intro p h
          exact h
        · constructor
          · intro h
            exact h
          · rintro h ⟨_, c⟩
            rw [h] at c
            contradiction,
      ⟩
    ⟩
  | none =>
    match O_root_def : O.1.root with
    | .terminal b' =>
        ⟨⟨⟨s0.size, s0.heap, s0.cache.insert O.1.root (.inl b')⟩, .inl b'⟩, by
          simp only
          constructor
          · exact insert_terminal_invariant s0 inv O_root_def
          · constructor
            · simp only [O_root_def, Std.HashMap.getElem?_insert_self]
            · constructor
              · exact .refl
              ·
                intro k
                constructor
                · intro p hp
                  rw [← hp]
                  simp only [Std.HashMap.getElem?_insert, beq_iff_eq, ite_eq_right_iff]
                  intro contra
                  subst contra
                  rw [hc] at hp
                  contradiction
                · constructor
                  · simp only [getElem?_eq_none_iff, Std.HashMap.mem_insert, beq_iff_eq, not_or,
                      and_imp, imp_self, implies_true]
                  · rintro h1 ⟨p, hp⟩
                    simp only [Std.HashMap.getElem?_insert,beq_iff_eq] at hp
                    split at hp
                    next heq =>
                      subst heq
                      simp only [O_root_def]
                      constructor
                    next heq => rw [h1] at hp; contradiction
        ⟩
    | .node j =>
        if hlt : O.1.heap[j].var = i
        then
          if hb : b
          then
            let ⟨⟨sl, rl⟩, ⟨invl, hl, hsl, hlp⟩⟩ := restrict_helper (O.high O_root_def) b i s0 inv
            ⟨ ⟨⟨sl.size, sl.heap, sl.cache.insert O.1.root rl⟩, rl⟩,
              by
                subst hlt
                constructor
                · intro k p
                  simp only
                  intro hkp
                  simp only [Std.HashMap.getElem?_insert,beq_iff_eq] at hkp
                  split at hkp
                  next heq =>
                    subst heq
                    injection hkp with hinj
                    subst hinj
                    constructor
                    · intro j' hj1 hrj
                      subst hrj
                      have that : O.1.heap[j].var.1 < (Pointer.toVar O.1.heap (O.high O_root_def).1.root).1 := by
                        have := OBdd.var_lt_high_var (O := O) (h := O_root_def)
                        simp only [OBdd.var, Nat.succ_eq_add_one, Bdd.var, OBdd.high_heap_eq_heap,
                          Fin.val_fin_lt] at this
                        rw [O_root_def] at this
                        simp only [Pointer.toVar] at this
                        exact this
                      have := (invl.2 _ _ hl).1 _ hj1 rfl
                      split at this
                      next hsp =>
                        rw [← hsp] at that
                        absurd that
                        simp only [Nat.succ_eq_add_one, OBdd.high_heap_eq_heap, lt_self_iff_false,
                          not_false_eq_true]
                      next hsp =>
                        simp_all only [getElem?_eq_none_iff,
                          Fin.getElem_fin, forall_exists_index,
                          Nat.succ_eq_add_one, Pointer.toVar_node_eq,
                          gt_iff_lt, ite_true]
                        exact that
                    · use O.2
                      have := (invl.2 _ _ hl).2.2
                      use this.1
                      use this.2.1
                      rw [this.2.2]
                      have triv {ho} : ⟨{ heap := O.1.heap, root := O.1.root }, ho⟩ = O := rfl
                      generalize_proofs at *
                      rw [triv]
                      have that := OBdd.evaluate_node'' O_root_def
                      rw [that]
                      rw [Nary.restrict_if]
                      simp only [OBdd.high_heap_eq_heap, hb, Fin.getElem_fin]
                      ext I
                      conv =>
                        rhs
                        congr
                        simp only [Nary.restrict, Vector.getElem_set_self]
                      rfl
                  next heq => exact (invl.2 _ _ hkp),
              by simp only [O_root_def, Std.HashMap.getElem?_insert_self],
              by exact hsl,
              by
                intro k
                constructor
                · intro p hkp
                  simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
                  split
                  next heq =>
                    subst heq
                    rw [hkp] at hc
                    contradiction
                  next => exact (hlp k).1 p hkp
                · constructor
                  · simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
                    split
                    next heq =>
                      subst heq
                      simp only [reduceCtorEq, getElem?_eq_none_iff, IsEmpty.forall_iff]
                    next => exact (hlp k).2.1
                  · simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
                    split
                    next heq =>
                      subst heq
                      rw [hc]
                      simp only [Option.some.injEq, exists_eq', forall_const, O_root_def]
                      left
                    next =>
                      intro hkn hhh
                      rw [← O_root_def]
                      trans (O.high O_root_def).1.root
                      · exact OBdd.reachable_of_edge (Bdd.edge_of_high O.1 (h := O_root_def))
                      · exact (hlp k).2.2 hkn hhh
            ⟩
          else
            let ⟨⟨sl, rl⟩, ⟨invl, hl, hsl, hlp⟩⟩ := restrict_helper (O.low O_root_def) b i s0 inv
            ⟨⟨⟨sl.size, sl.heap, sl.cache.insert O.1.root rl⟩, rl⟩,
              by
                subst hlt
                constructor
                · intro k p
                  simp only
                  intro hkp
                  simp only [Std.HashMap.getElem?_insert,beq_iff_eq] at hkp
                  split at hkp
                  next heq =>
                    subst heq
                    injection hkp with hinj
                    subst hinj
                    constructor
                    · intro j' hj1 hrj
                      subst hrj
                      have that : O.1.heap[j].var.1 < (Pointer.toVar O.1.heap (O.low O_root_def).1.root).1 := by
                        have := OBdd.var_lt_low_var (O := O) (h := O_root_def)
                        simp only [OBdd.var, Nat.succ_eq_add_one, Bdd.var, OBdd.low_heap_eq_heap,
                          Fin.val_fin_lt] at this
                        rw [O_root_def] at this
                        simp only [Pointer.toVar] at this
                        exact this
                      have := (invl.2 _ _ hl).1 _ hj1 rfl
                      split at this
                      next hsp =>
                        rw [← hsp] at that
                        absurd that
                        simp only [Nat.succ_eq_add_one, OBdd.low_heap_eq_heap, lt_self_iff_false,
                          not_false_eq_true]
                      next hsp =>
                        simp_all only [getElem?_eq_none_iff,
                          Fin.getElem_fin, OBdd.low_heap_eq_heap, forall_exists_index,
                          Nat.succ_eq_add_one, Pointer.toVar_node_eq, gt_iff_lt, ite_true]
                    · use O.2
                      have := (invl.2 _ _ hl).2.2
                      use this.1
                      use this.2.1
                      rw [this.2.2]
                      have triv {ho} : ⟨{ heap := O.1.heap, root := O.1.root }, ho⟩ = O := rfl
                      generalize_proofs at *
                      rw [triv]
                      have that := OBdd.evaluate_node'' O_root_def
                      rw [that]
                      rw [Nary.restrict_if]
                      simp only [OBdd.low_heap_eq_heap, hb, Fin.getElem_fin]
                      ext I
                      conv =>
                        rhs
                        congr
                        simp only [Nary.restrict, Vector.getElem_set_self]
                      rfl
                  next heq => exact (invl.2 _ _ hkp),
              by simp only [O_root_def, Std.HashMap.getElem?_insert_self],
              by exact hsl,
              by
                intro k
                constructor
                · intro p hkp
                  simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
                  split
                  next heq =>
                    subst heq
                    rw [hkp] at hc
                    contradiction
                  next => exact (hlp k).1 p hkp
                · constructor
                  · simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
                    split
                    next heq =>
                      subst heq
                      simp only [reduceCtorEq, getElem?_eq_none_iff, IsEmpty.forall_iff]
                    next => exact (hlp k).2.1
                  · simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
                    split
                    next heq =>
                      subst heq
                      rw [hc]
                      simp only [Option.some.injEq, exists_eq', forall_const, O_root_def]
                      left
                    next =>
                      intro hkn hhh
                      rw [← O_root_def]
                      trans (O.low O_root_def).1.root
                      · exact OBdd.reachable_of_edge (Bdd.edge_of_low O.1 (h := O_root_def))
                      · exact (hlp k).2.2 hkn hhh
          ⟩
        else
          let ⟨⟨sl, rl⟩, ⟨invl, hl, hsl, hlp⟩⟩ := restrict_helper (O.low O_root_def) b i s0 inv
          let ⟨⟨sh, rh⟩, ⟨invh, hh, hsh, hhp⟩⟩ := restrict_helper (O.high O_root_def) b i sl invl
          let ⟨r, ⟨invv, hv, hsv, hvp⟩⟩ :=
            heap_push (O := O)
              ⟨⟨O.1.heap[j].var.1, by omega⟩, rl, rh⟩ sh invh
              (by
                use (O.low O_root_def).1.root
                simp only
                exact (hhp _).1 _ hl
              )
              ⟨_, hh⟩
              (by
                simp only
                rw [O_root_def]
                simp only [Fin.getElem_fin] at hlt
                simp only [Nat.succ_eq_add_one, Pointer.toVar_node_eq, Fin.getElem_fin,
                  gt_iff_lt, lt_self_iff_false, if_false_left, and_true]
                omega
              )
              (by
                intro j' hj1
                simp only [Fin.getElem_fin]
                intro hj2
                have := (hhp _).1 _ hl
                simp only at this
                rw [hj2] at this
                have that := (invh.2 _ (.inr j') this).1 _ hj1 rfl
                simp only at that
                have hll : O.1.heap[j.1].var.1 < (Pointer.toVar O.1.heap (O.low O_root_def).1.root).1 := by
                  have := OBdd.var_lt_low_var (O := O) (h := O_root_def)
                  simp only [OBdd.var, Nat.succ_eq_add_one, Bdd.var, OBdd.low_heap_eq_heap,
                    Fin.val_fin_lt] at this
                  rw [O_root_def] at this
                  nth_rw 1 [Pointer.toVar] at this
                  simp_rw [Fin.lt_def, Fin.getElem_fin] at this
                  convert this using 1
                split at that
                next =>
                  trans (Pointer.toVar O.1.heap (O.low O_root_def).1.root).1
                  · exact hll
                  · exact that
                next =>
                  rw [that]
                  exact hll
              )
              (by
                intro j' hj1
                simp only [Fin.getElem_fin]
                intro hj2
                have that := (invh.2 _ _ hh).1 _ hj1 hj2
                have hll : O.1.heap[j.1].var.1 < (Pointer.toVar O.1.heap (O.high O_root_def).1.root).1 := by
                  have := OBdd.var_lt_high_var (O := O) (h := O_root_def)
                  simp only [OBdd.var, Nat.succ_eq_add_one, Bdd.var, OBdd.high_heap_eq_heap,
                    Fin.val_fin_lt] at this
                  rw [O_root_def] at this
                  nth_rw 1 [Pointer.toVar] at this
                  simp_rw [Fin.lt_def, Fin.getElem_fin] at this
                  convert this using 1
                split at that
                next =>
                  trans (Pointer.toVar O.1.heap (O.high O_root_def).1.root).1
                  · exact hll
                  · exact that
                next =>
                  rw [that]
                  exact hll
              )
              (by
                intro h0 h1
                symm
                rw [OBdd.evaluate_node'' O_root_def]
                rw [Nary.restrict_if]
                generalize_proofs at *
                conv =>
                  rhs
                  rw [OBdd.evaluate_node']
                simp only [Fin.getElem_fin, Fin.eta]
                ext I
                congr 1
                · simp only [Nary.restrict, cook_heap, RawNode.cook, Fin.getElem_fin,
                  Vector.getElem_ofFn, Vector.getElem_push_eq, eq_iff_iff, Bool.coe_iff_coe]
                  exact Vector.getElem_set_ne _ _ (fun contra ↦ by simp only [Fin.val_eq_val] at contra; rw [contra] at hlt; contradiction)
                · conv =>
                    rhs
                    congr
                    congr
                    congr
                    rfl
                    simp [cook_heap, RawNode.cook]
                    rfl
                    rfl
                  symm
                  have h := invh.2 (O.high O_root_def).1.root rh hh
                  rcases h with ⟨h1, h2, h3, h4, h5⟩
                  simp only [OBdd.high_heap_eq_heap] at h5
                  refine Eq.trans ?_ (congrFun h5 I)
                  exact congrFun (push_evaluate (hq := h3)
                    (hp := RawPointer.bounded_of_le h3 (by omega))
                    (ho := push_ordered h4) (hu := h4)) I
                · conv =>
                    rhs
                    congr
                    congr
                    congr
                    rfl
                    simp [cook_heap, RawNode.cook]
                    rfl
                    rfl
                  symm
                  have : sh.cache[(O.low O_root_def).1.root]? = some rl := by
                    apply (hhp _).1
                    exact hl
                  have h := invh.2 (O.low O_root_def).1.root rl this
                  rcases h with ⟨h1, h2, h3, h4, h5⟩
                  simp only [OBdd.high_heap_eq_heap] at h5
                  refine Eq.trans ?_ (congrFun h5 I)
                  exact congrFun (push_evaluate (hq := h3)
                    (hp := RawPointer.bounded_of_le h3 (by omega))
                    (ho := push_ordered h4) (hu := h4)) I
              )
              (by
                cases heq : sh.cache[O.1.root]? with
                | none => rfl
                | some val =>
                  cases heqq : sl.cache[O.1.root]? with
                  | none =>
                    have := ((hhp _).2.2 heqq ⟨val, heq⟩)
                    simp only [OBdd.high_heap_eq_heap] at this
                    absurd this
                    apply OBdd.not_oedge_reachable
                    exact oedge_of_high
                  | some val =>
                    have := ((hlp _).2.2 hc ⟨_, heqq⟩)
                    simp only [OBdd.low_heap_eq_heap] at this
                    absurd this
                    apply OBdd.not_oedge_reachable
                    exact oedge_of_low
              )
          ⟨ r,
            invv,
            (by rw [O_root_def] at hv; exact hv),
            .trans hsl (.trans hsh hsv),
            by
              intro k
              constructor
              · intro p hp
                apply (hvp _).1
                apply (hhp _).1
                apply (hlp _).1
                exact hp
              · constructor
                · intro hk
                  apply (hlp _).2.1
                  apply (hhp _).2.1
                  apply (hvp _).2.1
                  exact hk
                · intro hk hkp
                  rw [← O_root_def]
                  cases heq : sh.cache[k]? with
                  | none =>
                    apply (hvp _).2.2 heq hkp
                  | some w =>
                    cases heqq : sl.cache[k]? with
                    | none =>
                      have := (hhp _).2.2 heqq ⟨_, heq⟩
                      · trans (O.high O_root_def).1.root
                        · apply OBdd.reachable_of_edge
                          exact oedge_of_high.2
                        · exact this
                    | some ww =>
                      have := (hlp _).2.2 hk ⟨_, heqq⟩
                      · trans (O.low O_root_def).1.root
                        · apply OBdd.reachable_of_edge
                          exact oedge_of_low.2
                        · exact this
          ⟩
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
def orestrict (b : Bool) (i : Fin n) (O : OBdd n m) : (s : Nat) × { W : OBdd n s // W.evaluate = Nary.restrict O.evaluate b i } :=
  let ⟨⟨⟨siz, heap, _⟩, root⟩, h1, h2⟩:= restrict_helper O b i initial inv_initial
  ⟨ siz, ⟨⟨cook_heap heap h1.1, root.cook (h1.2 _ root h2.1).2.2.1⟩, (h1.2 _ root h2.1).2.2.2.1⟩, (h1.2 _ root h2.1).2.2.2.2 ⟩
end Restrict


