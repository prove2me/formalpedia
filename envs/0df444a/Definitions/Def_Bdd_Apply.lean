-- Prove2me | Definitions.Def_Bdd_Apply
-- name    : Bdd_Apply
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:09:17.573405+00:00
-- url     : https://prove2.me/theorems/b83a580b-6d1d-487b-bd6b-01e95be8e4c7
-- title:
--   Apply
-- statement:
--   Definitions and structural lemmas for Apply, from Eshel Yaron and contributors's pinned Correctness of binary decision diagrams for CNF formulas development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Apply.lean

import Definitions.Def_Bdd_Basic
import Std.Data.HashMap.Lemmas
import Theorems.Thm_Bdd_ordered_of_low_high_ordered
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_OBdd_evaluate_eq_evaluate_of_ordered_heap_all_reachable_eq
import Theorems.Thm_OBdd_not_oedge_reachable
import Theorems.Thm_OBdd_var_lt_high_var
import Theorems.Thm_OBdd_var_lt_low_var
import Theorems.Thm_P2M_OBdd_evaluate_node___75814e9183f4
import Theorems.Thm_RawBdd_RawNode_cook_equiv
import Theorems.Thm_RawBdd_RawPointer_cook_equiv
import Theorems.Thm_RawBdd_cook_high
import Theorems.Thm_RawBdd_cook_low
import Theorems.Thm_RawBdd_push_evaluate
import Theorems.Thm_RawBdd_push_ordered
attribute [local simp] Nary.restrict_const


set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered RawBdd.RawPointer RawBdd.RawPointer.Bounded Subrelation
namespace Apply
open RawBdd
structure State (n) (n') (m) (m') where
  size : Nat
  heap : Vector (RawNode (max n n')) size
  cache : Std.HashMap (Pointer m × Pointer m') RawPointer
def initial : State n n' m m' := ⟨_, (Vector.emptyWithCapacity (m ⊔ m')), Std.HashMap.emptyWithCapacity (m ⊔ m')⟩
@[simp]
lemma toVar_or_terminal_eq {n m} (w : Vector (Node n m) m) : toVar_or w (.terminal b) i = i := rfl
@[simp]
lemma toVar_or_node_eq {n m} (w : Vector (Node n m) m) {j} : toVar_or w (.node j) i = w[j].var := rfl
def Invariant (op : Bool → Bool → Bool) (O : OBdd n m) (U : OBdd n' m') (r : State n n' m m') :=
  ∃ hh : (∀ i : Fin r.size, RawNode.Bounded i r.heap[i]),
    ∀ (k : (Pointer m × Pointer m')) (p : RawPointer),
      r.cache[k]? = some p →
      (∀ j h, p = .inr j → (r.heap[j]'h).va.1 =
        (toVar_or O.1.heap k.1 (n ⊔ n')) ⊓ (toVar_or U.1.heap k.2 (n ⊔ n'))) ∧
      ∃ hk1 : Bdd.Ordered ⟨O.1.heap, k.1⟩,
        ∃ hk2 : Bdd.Ordered ⟨U.1.heap, k.2⟩,
          ∃ hp : p.Bounded r.size,
            ∃ o : Bdd.Ordered ⟨cook_heap r.heap hh, p.cook hp⟩,
              ∀ I,
                OBdd.evaluate ⟨⟨cook_heap r.heap hh, p.cook hp⟩, o⟩ I =
                op
                  (OBdd.evaluate ⟨⟨O.1.heap, k.1⟩, hk1⟩ (Vector.cast (by simp) (I.take n)))
                  (OBdd.evaluate ⟨⟨U.1.heap, k.2⟩, hk2⟩ (Vector.cast (by simp) (I.take n')))
lemma inv_initial {op} {O : OBdd n m} {U : OBdd n' m'} : Invariant op O U initial := by
  constructor
  · intro k p hp
    simp only [initial, Std.HashMap.getElem?_emptyWithCapacity, reduceCtorEq] at hp
  · rintro ⟨_, c⟩
    simp only [initial, not_lt_zero] at c
def cache_get (O_root : Pointer m) (U_root : Pointer m') (s : (State n n' m m')) : (Option RawPointer) :=
  s.cache[(⟨O_root, U_root⟩ : (Pointer m × Pointer m'))]?
lemma heap_push_aux {n n' m m' : Nat} {op : Bool → Bool → Bool}
    {O : OBdd n m} {U : OBdd n' m'} {N : RawNode (max n n')} (s : (State n n' m m')) (inv : Invariant op O U s)
    (hNl : ∃ k : Pointer m × Pointer m', s.cache[k]? = some N.lo)
    (hNh : ∃ k : Pointer m × Pointer m', s.cache[k]? = some N.hi)
    (hNv : N.va.1 = (toVar_or O.1.heap O.1.root (n ⊔ n')) ⊓ (toVar_or U.1.heap U.1.root (n ⊔ n')))
    (hxl : ∀ j h (_ : N.lo = .inr j), N.va.1 < (s.heap[j]'h).va.1)
    (hxh : ∀ j h (_ : N.hi = .inr j), N.va.1 < (s.heap[j]'h).va.1)
    (hh : ∀ h0 (h1 : Bdd.Ordered _) (I : Vector Bool (max n n')),
            OBdd.evaluate ⟨{ heap := cook_heap (s.heap.push N) h0, root := Pointer.node ⟨s.size, by simp⟩ }, h1⟩ I =
            op (O.evaluate (Vector.cast (by omega) (I.extract 0 n))) (U.evaluate (Vector.cast (by omega) (I.extract 0 n')))) :
    Invariant op O U
      { size := s.size + 1, heap := s.heap.push N, cache := s.cache.insert (O.1.root, U.1.root) (Sum.inr s.size) } := by
  rcases hNl with ⟨kl, hkl⟩
  rcases hNh with ⟨kh, hkh⟩
  have hN : RawNode.Bounded s.size N := by
    simp only [RawNode.Bounded]
    constructor
    · exact (inv.2 kl N.lo hkl).2.2.2.1
    · exact (inv.2 kh N.hi hkh).2.2.2.1
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
    simp only
    constructor
    · intro j hs hj
      rw [Vector.getElem_push]
      split
      next heqq =>
        injection hp with hpp
        rw [hj] at hpp
        injection hpp with hppp
        rw [hppp] at heqq
        absurd heqq
        simp only [lt_self_iff_false, not_false_eq_true]
      next heqq =>
        exact hNv
    use O.2, U.2
    injection hp with hpe
    subst hpe
    have hb : RawPointer.Bounded (s.size + 1) (Sum.inr s.size) := by intro i hi; injection hi with hie; subst hie; simp
    use hb
    have hoo : Bdd.Ordered ⟨cook_heap (s.heap.push N) this, RawPointer.cook (Sum.inr s.size) hb⟩ := by
      apply Bdd.ordered_of_low_high_ordered rfl
      · simp only [Bdd.low, cook_heap]
        simp only [Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_push_eq]
        rw [← cook_low]
        swap; apply RawPointer.bounded_of_le (inv.2 kl N.lo hkl).2.2.2.1; simp only [le_add_iff_nonneg_right, zero_le]
        rcases (inv.2 kl N.lo hkl).2.2.2 with that
        apply push_ordered
        · exact this
        · exact that.2.1
      ·
        simp [Nat.succ_eq_add_one, Bdd.var, cook_heap, Bdd.low, RawPointer.cook]
        cases heq : N.lo with
        | inl val =>
          rw [← cook_low]
          simp_rw [heq]
          · simp only [RawPointer.cook, Nat.succ_eq_add_one, Pointer.toVar, RawNode.cook,
            Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_push_eq, Fin.lt_def,
            Fin.val_last, lt_sup_iff]
            omega
          · apply RawPointer.bounded_of_le (inv.2 kl N.lo hkl).2.2.2.1
            simp
        | inr val =>
          have hvs : val < s.size := by
            apply RawPointer.bounded_of_le (inv.2 kl N.lo hkl).2.2.2.1 .refl heq
          rw [← cook_low]
          simp_rw [heq]
          · simp only [RawNode.cook, RawPointer.cook, Nat.succ_eq_add_one,
              Fin.getElem_fin, Vector.getElem_ofFn, Pointer.toVar]
            simp only [Vector.getElem_push_eq, Fin.mk_lt_mk, Fin.val_fin_lt, gt_iff_lt]
            rw [Vector.getElem_push_lt]
            · have hvs : val < s.size := by
                apply RawPointer.bounded_of_le (inv.2 kl N.lo hkl).2.2.2.1 .refl heq
              exact hxl _ hvs heq
            · exact hvs
          · apply RawPointer.bounded_of_le (inv.2 kl N.lo hkl).2.2.2.1
            simp only [le_add_iff_nonneg_right, zero_le]
      · simp only [Bdd.high, cook_heap]
        simp only [Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_push_eq]
        rw [← cook_high]
        swap; apply RawPointer.bounded_of_le (inv.2 kh N.hi hkh).2.2.2.1; simp only [le_add_iff_nonneg_right, zero_le]
        rcases (inv.2 kh N.hi hkh).2.2.2 with that
        apply push_ordered
        · exact this
        · exact that.2.1
      ·
        simp [Nat.succ_eq_add_one, Bdd.var, cook_heap, Bdd.high, RawPointer.cook]
        cases heq : N.hi with
        | inl val =>
          rw [← cook_high]
          simp_rw [heq]
          simp only [RawPointer.cook, Nat.succ_eq_add_one,
            Pointer.toVar]
          simp only [RawNode.cook, Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_push_eq,
            Fin.lt_def, Fin.val_last, lt_sup_iff]
          omega
          apply RawPointer.bounded_of_le (inv.2 kh N.hi hkh).2.2.2.1
          simp
        | inr val =>
          have hvs : val < s.size := by
            apply RawPointer.bounded_of_le (inv.2 _ _ hkh).2.2.2.1 .refl heq
          rw [← cook_high]
          simp_rw [heq]
          simp only [RawNode.cook, RawPointer.cook]
          simp only [Pointer.toVar, Nat.succ_eq_add_one, Fin.getElem_fin, Vector.getElem_ofFn,
            Vector.getElem_push_eq, Fin.mk_lt_mk, Fin.val_fin_lt, gt_iff_lt]
          rw [Vector.getElem_push_lt]
          exact hxh _ hvs heq
          apply RawPointer.bounded_of_le (inv.2 kh N.hi hkh).2.2.2.1; simp only [le_add_iff_nonneg_right, zero_le]
    use hoo
    rw [show ⟨{ heap := U.1.heap, root := U.1.root }, _⟩ =  U by rfl]
    rw [show ⟨{ heap := O.1.heap, root := O.1.root }, _⟩ =  O by rfl]
    simp only [RawPointer.cook]
    intro I
    apply hh _ hoo
  next heq =>
    constructor
    · intro j hs hj
      rw [hj] at hp
      rcases (inv.2 k _ hp) with ⟨inv1, inv2⟩
      have := inv1 j (inv2.2.2.1 rfl) rfl
      rw [Vector.getElem_push_lt (inv2.2.2.1 rfl)]
      exact this
    rcases (inv.2 k p hp) with that
    use that.2.1
    use that.2.2.1
    have hb : ∀ {i}, p = Sum.inr i → i < s.size + 1 :=
      RawPointer.bounded_of_le that.2.2.2.1 (by simp only [le_add_iff_nonneg_right, zero_le])
    use hb
    have ho : Bdd.Ordered { heap := cook_heap (s.heap.push N) this, root := p.cook hb } := push_ordered that.2.2.2.2.1
    use ho
    intro I
    calc _
      _ = OBdd.evaluate ⟨{ heap := cook_heap (s.heap) inv.1, root := p.cook that.2.2.2.1 }, that.2.2.2.2.1⟩ I := by
        rw [OBdd.evaluate_eq_evaluate_of_ordered_heap_all_reachable_eq]
        · simp only [Fin.getElem_fin]
          intro j hj
          use (by omega)
          simp [cook_heap]
          exact RawNode.cook_equiv
        · simp only [RawPointer.cook_equiv]
    exact that.2.2.2.2.2 I
def heap_push {n n' m m' : Nat} {op : Bool → Bool → Bool}
    {O : OBdd n m} {U : OBdd n' m'} (N : RawNode (n ⊔ n')) (s : (State n n' m m')) (inv : Invariant op O U s)
    (hNl : ∃ k : Pointer m × Pointer m', s.cache[k]? = some N.lo)
    (hNh : ∃ k : Pointer m × Pointer m', s.cache[k]? = some N.hi)
    (hNv : N.va.1 = (toVar_or O.1.heap O.1.root (n ⊔ n')) ⊓ (toVar_or U.1.heap U.1.root (n ⊔ n')))
    (hxl : ∀ j h (_ : N.lo = .inr j), N.va.1 < (s.heap[j]'h).va.1)
    (hxh : ∀ j h (_ : N.hi = .inr j), N.va.1 < (s.heap[j]'h).va.1)
    (hh : ∀ h0 (h1 : Bdd.Ordered _) (I : Vector Bool (max n n')),
            OBdd.evaluate ⟨{ heap := cook_heap (s.heap.push N) h0, root := Pointer.node ⟨s.size, by simp⟩ }, h1⟩ I =
            op (O.evaluate (Vector.cast (by omega) (I.extract 0 n))) (U.evaluate (Vector.cast (by omega) (I.extract 0 n'))))
            (hc : s.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? = none ) :
    { r : State n n' m m' × RawPointer //
      (Invariant op O U r.1) ∧
      (r.1.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? = some r.2) ∧
      s.size ≤ r.1.size ∧
      (∀ (k : Pointer m × Pointer m'),
        (∀ p, s.cache[k]? = some p → r.1.cache[k]? = some p) ∧
        (r.1.cache[k]? = none → s.cache[k]? = none) ∧
        (s.cache[k]? = none → (∃ p, r.1.cache[k]? = some p) → Pointer.Reachable O.1.heap O.1.root k.1 ∧ Pointer.Reachable U.1.heap U.1.root k.2))
    } :=
  ⟨⟨⟨s.size + 1, s.heap.push N, s.cache.insert ⟨O.1.root, U.1.root⟩ (.inr s.size)⟩, .inr s.size⟩, by
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
              next heqq => subst heqq; constructor <;> left
              next heqq => rw [hk] at hq; contradiction
  ⟩
lemma insert_terminal_invariant {n n' m m' : Nat} {op : Bool → Bool → Bool}
    {O : OBdd n m} {U : OBdd n' m'} {b b' : Bool} (s0 : State n n' m m') (inv : Invariant op O U s0) (ho : O.1.root = .terminal b) (hu : U.1.root = .terminal b'):
    Invariant op O U { size := s0.size, heap := s0.heap, cache := s0.cache.insert (O.1.root, U.1.root) (Sum.inl (op b b')) } := by
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
    use O.2, U.2
    injection hp with hpe
    subst hpe
    use (fun contra ↦ by contradiction)
    simp [RawPointer.cook, ho, hu, Bdd.Ordered_of_terminal]
  next =>
    constructor
    · exact (inv.2 _ _ hp).1
    exact (inv.2 _ _ hp).2
lemma op_if1 (op : Bool → Bool → Bool) {c l rt rf : Bool} :
    op l (if c then rt else rf) = if c then (op l rt) else (op l rf) :=
      apply_ite (op l) (c = true) rt rf
lemma op_if2 (op : Bool → Bool → Bool) {c lt lf r : Bool} :
    op  (if c then lt else lf) r = if c then (op lt r) else (op lf r) := by
  split
  next h =>
    subst h
    simp_all only
  next h => simp_all only [Bool.not_eq_true]
lemma op_if3 (op : Bool → Bool → Bool) {c lt lf rt rf : Bool} :
    op (if c then lt else lf) (if c then rt else rf) = if c then (op lt rt) else (op lf rf) := by
  split
  next h =>
    subst h
    simp_all only
  next h => simp_all only [Bool.not_eq_true]
lemma aux_lt1_low {O : OBdd n m} {U : OBdd n' m'} (O_root_def : O.1.root = .terminal b) (U_root_def : U.1.root = .node j') :
    U.1.heap[j'].var.1 <
    min (toVar_or O.1.heap O.1.root (max n n'))
        (toVar_or U.1.heap (U.low U_root_def).1.root (max n n')) := by
  have := OBdd.var_lt_low_var (h := U_root_def)
  simp_all [OBdd.var, toVar_or, Pointer.toVar]
  split <;> simp_all
lemma aux_lt1_high {O : OBdd n m} {U : OBdd n' m'} (O_root_def : O.1.root = .terminal b) (U_root_def : U.1.root = .node j') :
    U.1.heap[j'].var.1 <
    min (toVar_or O.1.heap O.1.root (max n n'))
        (toVar_or U.1.heap (U.high U_root_def).1.root (max n n')) := by
  have := OBdd.var_lt_low_var (h := U_root_def)
  have := OBdd.var_lt_high_var (h := U_root_def)
  simp_all [OBdd.var, toVar_or, Pointer.toVar]
  split <;> simp_all
lemma aux_lt2_low {O : OBdd n m} {U : OBdd n' m'} (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .terminal b') :
    O.1.heap[j].var.1 <
    min (toVar_or O.1.heap (O.low O_root_def).1.root (max n n'))
        (toVar_or U.1.heap U.1.root (max n n')) := by
  have := OBdd.var_lt_low_var (h := O_root_def)
  have := OBdd.var_lt_high_var (h := O_root_def)
  simp_all [OBdd.var, toVar_or, Pointer.toVar]
  split <;> simp_all
lemma aux_lt2_high {O : OBdd n m} {U : OBdd n' m'} (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .terminal b') :
    O.1.heap[j].var.1 <
    min (toVar_or O.1.heap (O.high O_root_def).1.root (max n n'))
        (toVar_or U.1.heap U.1.root (max n n')) := by
  have := OBdd.var_lt_low_var (h := O_root_def)
  have := OBdd.var_lt_high_var (h := O_root_def)
  simp_all [OBdd.var, toVar_or, Pointer.toVar]
  split <;> simp_all
lemma aux_lt3_low {O : OBdd n m} {U : OBdd n' m'} (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .node j') (hleq : O.1.heap[j].var.1 < U.1.heap[j'].var.1) :
    O.1.heap[j].var.1 <
    min (toVar_or O.1.heap (O.low O_root_def).1.root (max n n'))
        (toVar_or U.1.heap U.1.root (max n n')) := by
  have := OBdd.var_lt_low_var (h := O_root_def)
  have := OBdd.var_lt_high_var (h := O_root_def)
  have := OBdd.var_lt_low_var (h := U_root_def)
  have := OBdd.var_lt_high_var (h := U_root_def)
  simp_all [OBdd.var, toVar_or, Pointer.toVar]
  split <;> simp_all
lemma aux_lt3_high {O : OBdd n m} {U : OBdd n' m'} (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .node j') (hleq : O.1.heap[j].var.1 < U.1.heap[j'].var.1) :
    O.1.heap[j].var.1 <
    min (toVar_or O.1.heap (O.high O_root_def).1.root (max n n'))
        (toVar_or U.1.heap U.1.root (max n n')) := by
  have := OBdd.var_lt_low_var (h := O_root_def)
  have := OBdd.var_lt_high_var (h := O_root_def)
  have := OBdd.var_lt_low_var (h := U_root_def)
  have := OBdd.var_lt_high_var (h := U_root_def)
  simp_all [OBdd.var, toVar_or, Pointer.toVar]
  split <;> simp_all
lemma aux_lt4_low {O : OBdd n m} {U : OBdd n' m'} (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .node j') (hgeq : O.1.heap[j].var.1 > U.1.heap[j'].var.1) :
    U.1.heap[j'].var.1 <
    min (toVar_or O.1.heap O.1.root (max n n'))
        (toVar_or U.1.heap (U.low U_root_def).1.root (max n n')) := by
  have := OBdd.var_lt_low_var (h := O_root_def)
  have := OBdd.var_lt_high_var (h := O_root_def)
  have := OBdd.var_lt_low_var (h := U_root_def)
  have := OBdd.var_lt_high_var (h := U_root_def)
  simp_all [OBdd.var, toVar_or, Pointer.toVar]
  split <;> simp_all
lemma aux_lt4_high {O : OBdd n m} {U : OBdd n' m'} (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .node j') (hgeq : O.1.heap[j].var.1 > U.1.heap[j'].var.1) :
    U.1.heap[j'].var.1 <
    min (toVar_or O.1.heap O.1.root (max n n'))
        (toVar_or U.1.heap (U.high U_root_def).1.root (max n n')) := by
  have := OBdd.var_lt_low_var (h := O_root_def)
  have := OBdd.var_lt_high_var (h := O_root_def)
  have := OBdd.var_lt_low_var (h := U_root_def)
  have := OBdd.var_lt_high_var (h := U_root_def)
  simp_all [OBdd.var, toVar_or, Pointer.toVar]
  split <;> simp_all
lemma aux_lt5_low {O : OBdd n m} {U : OBdd n' m'} (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .node j') (heeq : O.1.heap[j].var.1 = U.1.heap[j'].var.1) :
    U.1.heap[j'].var.1 <
    min (toVar_or O.1.heap (O.low O_root_def).1.root (max n n'))
        (toVar_or U.1.heap (U.low U_root_def).1.root (max n n')) := by
  have h1 := OBdd.var_lt_low_var (h := O_root_def)
  have h2 := OBdd.var_lt_high_var (h := O_root_def)
  have h3 := OBdd.var_lt_low_var (h := U_root_def)
  have h4 := OBdd.var_lt_high_var (h := U_root_def)
  have h5 : U.1.heap[↑j'].var.1 < n + 1 := by omega
  simp_all [OBdd.var, toVar_or]
  split
  next heq =>
    split
    next heqq => simp_all
    next heqq => simp_all
  next heq =>
    split
    next heqq =>
      have h6 : (U.1.heap[↑j'].var.1) % (n + 1) = U.1.heap[↑j'].var.1 := by exact Nat.mod_eq_of_lt h5
      simp_all only [Fin.getElem_fin]
      simp_all
    next heqq =>
      have h6 : (U.1.heap[↑j'].var.1) % (n + 1) = U.1.heap[↑j'].var.1 := by exact Nat.mod_eq_of_lt h5
      simp_all only [Fin.getElem_fin]
      simp_all
lemma aux_lt5_high {O : OBdd n m} {U : OBdd n' m'} (O_root_def : O.1.root = .node j) (U_root_def : U.1.root = .node j') (heeq : O.1.heap[j].var.1 = U.1.heap[j'].var.1) :
    U.1.heap[j'].var.1 <
    min (toVar_or O.1.heap (O.high O_root_def).1.root (max n n'))
        (toVar_or U.1.heap (U.high U_root_def).1.root (max n n')) := by
  have h2 := OBdd.var_lt_high_var (h := O_root_def)
  have h3 := OBdd.var_lt_low_var (h := U_root_def)
  have h4 := OBdd.var_lt_high_var (h := U_root_def)
  have h5 : U.1.heap[↑j'].var.1 < n + 1 := by omega
  simp_all [OBdd.var, toVar_or]
  split
  next heq =>
    split
    next heqq => simp_all
    next heqq => simp_all
  next heq =>
    split
    next heqq =>
      have h6 : (U.1.heap[↑j'].var.1) % (n + 1) = U.1.heap[↑j'].var.1 := by exact Nat.mod_eq_of_lt h5
      simp_all only [Fin.getElem_fin]
      simp_all
    next heqq =>
      have h6 : (U.1.heap[↑j'].var.1) % (n + 1) = U.1.heap[↑j'].var.1 := by exact Nat.mod_eq_of_lt h5
      simp_all only [Fin.getElem_fin]
      simp_all
set_option maxHeartbeats 2000000 in
def apply_helper (op : (Bool → Bool → Bool)) (O : OBdd n m) (U : OBdd n' m') (s0 : State n n' m m') (inv : Invariant op O U s0) :
    { r : State n n' m m' × RawPointer //
      (Invariant op O U r.1) ∧
      (r.1.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? = some r.2) ∧
      (s0.size ≤ r.1.size) ∧
      (∀ (k : Pointer m × Pointer m'),
        (∀ p, s0.cache[k]? = some p → r.1.cache[k]? = some p) ∧
        (r.1.cache[k]? = none → s0.cache[k]? = none) ∧
        (s0.cache[k]? = none → (∃ p, r.1.cache[k]? = some p) → Pointer.Reachable O.1.heap O.1.root k.1 ∧ Pointer.Reachable U.1.heap U.1.root k.2))
    } :=
  match hc : cache_get O.1.root U.1.root s0 with
  | some root => ⟨⟨s0, root⟩, ⟨inv, hc, .refl, by grind only⟩⟩
  | none =>
    match O_root_def : O.1.root with
    | .terminal b =>
      match U_root_def : U.1.root with
      | .terminal b' =>
        ⟨⟨⟨s0.size, s0.heap, s0.cache.insert ⟨O.1.root, U.1.root⟩ (.inl (op b b'))⟩, .inl (op b b')⟩, by
          constructor
          · exact insert_terminal_invariant s0 inv O_root_def U_root_def
          · constructor
            · simp only [O_root_def, U_root_def, Std.HashMap.getElem?_insert_self]
            · constructor
              · exact .refl
              ·
                intro k
                constructor
                · intro p hp
                  simp only [cache_get] at hc
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
                      simp only [O_root_def, U_root_def]
                      constructor
                      · left
                      · left
                    next heq => rw [h1] at hp; contradiction
        ⟩
      | .node j' =>
        let ⟨⟨sl, rl⟩, ⟨invl, hl, hsl, hlp⟩⟩ := apply_helper op O (U.low U_root_def) s0 inv
        let ⟨⟨sh, rh⟩, ⟨invh, hh, hsh, hhp⟩⟩ := apply_helper op O (U.high U_root_def) sl invl
        let ⟨r, ⟨invv, hv, hsv, hvp⟩⟩ :=
          heap_push (O := O) (U := U)
            ⟨⟨U.1.heap[j'].var.1, by omega⟩, rl, rh⟩ sh invh
            (by
              use ⟨O.1.root, ((U.low U_root_def).1.root)⟩
              simp only
              exact (hhp _).1 _ hl
            )
            ⟨_, hh⟩
            (by
              simp only
              rw [O_root_def, U_root_def]
              simp only [Fin.getElem_fin, toVar_or, le_sup_iff, Fin.is_le', or_true,
                inf_of_le_right]
            )
            (by
              intro j hj1
              simp only [Fin.getElem_fin]
              intro hj2
              have := (hhp _).1 _ hl
              simp only at this
              rw [hj2] at this
              have that := (invh.2 _ (.inr j) this).1 _ hj1 rfl
              simp only at that
              rw [that]
              exact aux_lt1_low O_root_def U_root_def
            )
            (by
              intro j hj1
              simp only [Fin.getElem_fin]
              intro hj2
              have := (invh.2 _ _ hh).1 _ hj1 hj2
              rw [this]
              exact aux_lt1_high O_root_def U_root_def
            )
            (by
              intro h0 h1 I
              symm
              rw [OBdd.evaluate_node'' U_root_def]
              simp only
              rw [op_if1 op]
              simp only [OBdd.evaluate_node]
              congr 1
              · simp only [Nat.sub_zero, Fin.getElem_fin, Vector.getElem_cast, cook_heap,
                  RawNode.cook, Vector.getElem_ofFn, Vector.getElem_push_eq, eq_iff_iff,
                  Bool.coe_iff_coe]
                have := Vector.getElem_extract (as := I) (start := 0) (stop := n') (i := U.1.heap[j'.1].var.1) (by omega)
                simp only [Nat.sub_zero, zero_add] at this
                exact this
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
                have h := invh.2 ⟨O.1.root, (U.high U_root_def).1.root⟩ rh hh
                rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
                refine Eq.trans ?_ (h6 I)
                exact congrFun (push_evaluate (hq := h4) (hp := RawPointer.bounded_of_le h4 (by omega)) (h0 := h0) (ho := push_ordered h5) (hu := h5)) I
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
                have : sh.cache[(⟨O.1.root, (U.low U_root_def).1.root⟩ : Pointer m × Pointer m')]? = some rl := by
                  apply (hhp _).1
                  exact hl
                have h := invh.2 ⟨O.1.root, (U.low U_root_def).1.root⟩ rl this
                rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
                refine Eq.trans ?_ (h6 I)
                exact congrFun (push_evaluate (hq := h4) (hp := RawPointer.bounded_of_le h4 (by omega)) (h0 := h0) (ho := push_ordered h5) (hu := h5)) I
            )
            (by
              simp only [cache_get] at hc
              cases heq : sh.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
              | none => rfl
              | some val =>
                cases heqq : sl.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
                | none =>
                  have := ((hhp _).2.2 heqq ⟨val, heq⟩).2
                  simp only [OBdd.high_heap_eq_heap] at this
                  absurd this
                  apply OBdd.not_oedge_reachable
                  exact oedge_of_high
                | some val =>
                  have := ((hlp _).2.2 hc ⟨_, heqq⟩).2
                  simp only [OBdd.low_heap_eq_heap] at this
                  absurd this
                  apply OBdd.not_oedge_reachable
                  exact oedge_of_low
            )
        ⟨ r,
          invv,
          (by rw [O_root_def, U_root_def] at hv; exact hv),
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
                rw [← O_root_def, ← U_root_def]
                cases heq : sh.cache[k]? with
                | none =>
                  apply (hvp _).2.2 heq hkp
                | some w =>
                  cases heqq : sl.cache[k]? with
                  | none =>
                    have := (hhp _).2.2 heqq ⟨_, heq⟩
                    constructor
                    · exact this.1
                    · trans (U.high U_root_def).1.root
                      · apply OBdd.reachable_of_edge
                        exact oedge_of_high.2
                      · exact this.2
                  | some ww =>
                    have := (hlp _).2.2 hk ⟨_, heqq⟩
                    constructor
                    · exact this.1
                    · trans (U.low U_root_def).1.root
                      · apply OBdd.reachable_of_edge
                        exact oedge_of_low.2
                      · exact this.2
        ⟩
    | .node j =>
      match U_root_def : U.1.root with
      | .terminal b' =>
        let ⟨⟨sl, rl⟩, ⟨invl, hl, hsl, hlp⟩⟩ := apply_helper op (O.low O_root_def) U s0 inv
        let ⟨⟨sh, rh⟩, ⟨invh, hh, hsh, hhp⟩⟩ := apply_helper op (O.high O_root_def) U sl invl
        let ⟨r, ⟨invv, hv, hsv, hvp⟩⟩ :=
          heap_push (O := O) (U := U)
            ⟨⟨O.1.heap[j].var.1, by omega⟩, rl, rh⟩ sh invh
            ⟨_, (hhp _).1 _ hl⟩
            ⟨_, hh⟩
            (by
              simp only
              rw [O_root_def, U_root_def]
              simp only [Fin.getElem_fin, toVar_or, le_sup_iff, Fin.is_le', true_or, inf_of_le_left]
            )
            (by
              intro j hj1
              simp only [Fin.getElem_fin]
              intro hj2
              have := (hhp _).1 _ hl
              simp only at this
              rw [hj2] at this
              have that := (invh.2 _ (.inr j) this).1 _ hj1 rfl
              simp only at that
              rw [that]
              exact aux_lt2_low O_root_def U_root_def
            )
            (by
              intro j hj1
              simp only [Fin.getElem_fin]
              intro hj2
              have := (invh.2 _ _ hh).1 _ hj1 hj2
              rw [this]
              exact aux_lt2_high O_root_def U_root_def
            )
            (by
              intro h0 h1 I
              symm
              rw [OBdd.evaluate_node'' O_root_def]
              simp only
              rw [op_if2 op]
              simp only [OBdd.evaluate_node]
              congr 1
              · simp only [Nat.sub_zero, Fin.getElem_fin, Vector.getElem_cast, cook_heap,
                  RawNode.cook, Vector.getElem_ofFn, Vector.getElem_push_eq, eq_iff_iff,
                  Bool.coe_iff_coe]
                have := Vector.getElem_extract (as := I) (start := 0) (stop := n) (i := O.1.heap[j.1].var.1) (by omega)
                simp only [Nat.sub_zero, zero_add] at this
                exact this
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
                have h := invh.2 ⟨(O.high O_root_def).1.root, U.1.root⟩ rh hh
                rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
                refine Eq.trans ?_ (h6 I)
                exact congrFun (push_evaluate (hq := h4) (hp := RawPointer.bounded_of_le h4 (by omega)) (h0 := h0) (ho := push_ordered h5) (hu := h5)) I
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
                have : sh.cache[(⟨(O.low O_root_def).1.root, U.1.root⟩ : Pointer m × Pointer m')]? = some rl := by
                  apply (hhp _).1
                  exact hl
                have h := invh.2 ⟨(O.low O_root_def).1.root, U.1.root⟩ rl this
                rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
                refine Eq.trans ?_ (h6 I)
                exact congrFun (push_evaluate (hq := h4) (hp := RawPointer.bounded_of_le h4 (by omega)) (h0 := h0) (ho := push_ordered h5) (hu := h5)) I
            )
            (by
              simp only [cache_get] at hc
              cases heq : sh.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
              | none => rfl
              | some val =>
                cases heqq : sl.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
                | none =>
                  have := ((hhp _).2.2 heqq ⟨val, heq⟩).1
                  simp only [OBdd.high_heap_eq_heap] at this
                  absurd this
                  apply OBdd.not_oedge_reachable
                  exact oedge_of_high
                | some val =>
                  have := ((hlp _).2.2 hc ⟨_, heqq⟩).1
                  simp only [OBdd.low_heap_eq_heap] at this
                  absurd this
                  apply OBdd.not_oedge_reachable
                  exact oedge_of_low
            )
        ⟨ r,
          invv,
          (by rw [O_root_def, U_root_def] at hv; exact hv),
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
                rw [← O_root_def, ← U_root_def]
                cases heq : sh.cache[k]? with
                | none =>
                  apply (hvp _).2.2 heq hkp
                | some w =>
                  cases heqq : sl.cache[k]? with
                  | none =>
                    have := (hhp _).2.2 heqq ⟨_, heq⟩
                    constructor
                    · trans (O.high O_root_def).1.root
                      · apply OBdd.reachable_of_edge
                        exact oedge_of_high.2
                      · exact this.1
                    · exact this.2
                  | some ww =>
                    have := (hlp _).2.2 hk ⟨_, heqq⟩
                    constructor
                    · trans (O.low O_root_def).1.root
                      · apply OBdd.reachable_of_edge
                        exact oedge_of_low.2
                      · exact this.1
                    · exact this.2
        ⟩
      | .node j' =>
        if hlt : O.1.heap[j].var.1 < U.1.heap[j'].var.1
        then
          let ⟨⟨sl, rl⟩, ⟨invl, hl, hsl, hlp⟩⟩ := apply_helper op (O.low O_root_def) U s0 inv
          let ⟨⟨sh, rh⟩, ⟨invh, hh, hsh, hhp⟩⟩ := apply_helper op (O.high O_root_def) U sl invl
          let ⟨r, ⟨invv, hv, hsv, hvp⟩⟩ :=
            heap_push (O := O) (U := U)
              ⟨⟨O.1.heap[j].var.1, by omega⟩, rl, rh⟩ sh invh
              ⟨_, (hhp _).1 _ hl⟩
              ⟨_, hh⟩
              (by
                simp only
                rw [O_root_def, U_root_def]
                simp only [Fin.getElem_fin, toVar_or]
                exact Eq.symm (min_eq_left_of_lt hlt)
              )
              (by
                intro j'' hj1
                simp only [Fin.getElem_fin]
                intro hj2
                have := (hhp _).1 _ hl
                simp only at this
                rw [hj2] at this
                have that := (invh.2 _ _ this).1 _ hj1 rfl
                simp only at that
                rw [that]
                exact aux_lt3_low O_root_def U_root_def hlt
              )
              (by
                intro j'' hj1
                simp only [Fin.getElem_fin]
                intro hj2
                have := (invh.2 _ _ hh).1 _ hj1 hj2
                rw [this]
                exact aux_lt3_high O_root_def U_root_def hlt
              )
              (by
                intro h0 h1 I
                symm
                rw [OBdd.evaluate_node'' O_root_def]
                simp only
                rw [op_if2 op]
                simp only [OBdd.evaluate_node]
                congr 1
                · simp only [Nat.sub_zero, Fin.getElem_fin, Vector.getElem_cast, cook_heap,
                    RawNode.cook, Vector.getElem_ofFn, Vector.getElem_push_eq, eq_iff_iff,
                    Bool.coe_iff_coe]
                  have := Vector.getElem_extract (as := I) (start := 0) (stop := n) (i := O.1.heap[j.1].var.1) (by omega)
                  simp only [Nat.sub_zero, zero_add] at this
                  exact this
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
                  have h := invh.2 ⟨(O.high O_root_def).1.root, U.1.root⟩ rh hh
                  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
                  refine Eq.trans ?_ (h6 I)
                  exact congrFun (push_evaluate (hq := h4) (hp := RawPointer.bounded_of_le h4 (by omega)) (h0 := h0) (ho := push_ordered h5) (hu := h5)) I
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
                  have : sh.cache[(⟨(O.low O_root_def).1.root, U.1.root⟩ : Pointer m × Pointer m')]? = some rl := by
                    apply (hhp _).1
                    exact hl
                  have h := invh.2 ⟨(O.low O_root_def).1.root, U.1.root⟩ rl this
                  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
                  refine Eq.trans ?_ (h6 I)
                  exact congrFun (push_evaluate (hq := h4) (hp := RawPointer.bounded_of_le h4 (by omega)) (h0 := h0) (ho := push_ordered h5) (hu := h5)) I
              )
              (by
                simp only [cache_get] at hc
                cases heq : sh.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
                | none => rfl
                | some val =>
                  cases heqq : sl.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
                  | none =>
                    have := ((hhp _).2.2 heqq ⟨val, heq⟩).1
                    simp only [OBdd.high_heap_eq_heap] at this
                    absurd this
                    apply OBdd.not_oedge_reachable
                    exact oedge_of_high
                  | some val =>
                    have := ((hlp _).2.2 hc ⟨_, heqq⟩).1
                    simp only [OBdd.low_heap_eq_heap] at this
                    absurd this
                    apply OBdd.not_oedge_reachable
                    exact oedge_of_low
              )
          ⟨ r,
            invv,
            (by rw [O_root_def, U_root_def] at hv; exact hv),
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
                  rw [← O_root_def, ← U_root_def]
                  cases heq : sh.cache[k]? with
                  | none =>
                    apply (hvp _).2.2 heq hkp
                  | some w =>
                    cases heqq : sl.cache[k]? with
                    | none =>
                      have := (hhp _).2.2 heqq ⟨_, heq⟩
                      constructor
                      · trans (O.high O_root_def).1.root
                        · apply OBdd.reachable_of_edge
                          exact oedge_of_high.2
                        · exact this.1
                      · exact this.2
                    | some ww =>
                      have := (hlp _).2.2 hk ⟨_, heqq⟩
                      constructor
                      · trans (O.low O_root_def).1.root
                        · apply OBdd.reachable_of_edge
                          exact oedge_of_low.2
                        · exact this.1
                      · exact this.2
          ⟩
        else
          if hgeq : O.1.heap[j].var.1 > U.1.heap[j'].var.1
          then
            let ⟨⟨sl, rl⟩, ⟨invl, hl, hsl, hlp⟩⟩ := apply_helper op O (U.low U_root_def) s0 inv
            let ⟨⟨sh, rh⟩, ⟨invh, hh, hsh, hhp⟩⟩ := apply_helper op O (U.high U_root_def) sl invl
            let ⟨r, ⟨invv, hv, hsv, hvp⟩⟩ :=
              heap_push (O := O) (U := U)
                ⟨⟨U.1.heap[j'].var.1, by omega⟩, rl, rh⟩ sh invh
                ⟨_, (hhp _).1 _ hl⟩
                ⟨_, hh⟩
                (by
                  simp only
                  rw [O_root_def, U_root_def]
                  simp only [Fin.getElem_fin, toVar_or]
                  exact Eq.symm (min_eq_right_of_lt hgeq)
                )
                (by
                  intro j'' hj1
                  simp only [Fin.getElem_fin]
                  intro hj2
                  have := (hhp _).1 _ hl
                  simp only at this
                  rw [hj2] at this
                  have that := (invh.2 _ _ this).1 _ hj1 rfl
                  simp only at that
                  rw [that]
                  exact aux_lt4_low O_root_def U_root_def hgeq
                )
                (by
                  intro j'' hj1
                  simp only [Fin.getElem_fin]
                  intro hj2
                  have := (invh.2 _ _ hh).1 _ hj1 hj2
                  rw [this]
                  exact aux_lt4_high O_root_def U_root_def hgeq
                )
                (by
                  intro h0 h1 I
                  symm
                  rw [OBdd.evaluate_node'' U_root_def]
                  simp only
                  rw [op_if1 op]
                  simp only [OBdd.evaluate_node]
                  congr 1
                  · simp only [Nat.sub_zero, Fin.getElem_fin, Vector.getElem_cast, cook_heap,
                      RawNode.cook, Vector.getElem_ofFn, Vector.getElem_push_eq, eq_iff_iff,
                      Bool.coe_iff_coe]
                    have := Vector.getElem_extract (as := I) (start := 0) (stop := n') (i := U.1.heap[j'.1].var.1) (by omega)
                    simp only [Nat.sub_zero, zero_add] at this
                    exact this
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
                    have h := invh.2 ⟨O.1.root, (U.high U_root_def).1.root⟩ rh hh
                    rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
                    refine Eq.trans ?_ (h6 I)
                    exact congrFun (push_evaluate (hq := h4) (hp := RawPointer.bounded_of_le h4 (by omega)) (h0 := h0) (ho := push_ordered h5) (hu := h5)) I
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
                    have : sh.cache[(⟨O.1.root, (U.low U_root_def).1.root⟩ : Pointer m × Pointer m')]? = some rl := by
                      apply (hhp _).1
                      exact hl
                    have h := invh.2 ⟨O.1.root, (U.low U_root_def).1.root⟩ rl this
                    rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
                    refine Eq.trans ?_ (h6 I)
                    exact congrFun (push_evaluate (hq := h4) (hp := RawPointer.bounded_of_le h4 (by omega)) (h0 := h0) (ho := push_ordered h5) (hu := h5)) I
                )
                (by
                  simp only [cache_get] at hc
                  cases heq : sh.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
                  | none => rfl
                  | some val =>
                    cases heqq : sl.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
                    | none =>
                      have := ((hhp _).2.2 heqq ⟨val, heq⟩).2
                      simp only [OBdd.high_heap_eq_heap] at this
                      absurd this
                      apply OBdd.not_oedge_reachable
                      exact oedge_of_high
                    | some val =>
                      have := ((hlp _).2.2 hc ⟨_, heqq⟩).2
                      simp only [OBdd.low_heap_eq_heap] at this
                      absurd this
                      apply OBdd.not_oedge_reachable
                      exact oedge_of_low
                )
            ⟨ r,
              invv,
              (by rw [O_root_def, U_root_def] at hv; exact hv),
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
                    rw [← O_root_def, ← U_root_def]
                    cases heq : sh.cache[k]? with
                    | none =>
                      apply (hvp _).2.2 heq hkp
                    | some w =>
                      cases heqq : sl.cache[k]? with
                      | none =>
                        have := (hhp _).2.2 heqq ⟨_, heq⟩
                        constructor
                        · exact this.1
                        · trans (U.high U_root_def).1.root
                          · apply OBdd.reachable_of_edge
                            exact oedge_of_high.2
                          · exact this.2
                      | some ww =>
                        have := (hlp _).2.2 hk ⟨_, heqq⟩
                        constructor
                        · exact this.1
                        · trans (U.low U_root_def).1.root
                          · apply OBdd.reachable_of_edge
                            exact oedge_of_low.2
                          · exact this.2
            ⟩
          else
            let ⟨⟨sl, rl⟩, ⟨invl, hl, hsl, hlp⟩⟩ := apply_helper op (O.low O_root_def) (U.low U_root_def) s0 inv
            let ⟨⟨sh, rh⟩, ⟨invh, hh, hsh, hhp⟩⟩ := apply_helper op (O.high O_root_def) (U.high U_root_def) sl invl
            let ⟨r, ⟨invv, hv, hsv, hvp⟩⟩ :=
              heap_push (O := O) (U := U)
                ⟨⟨U.1.heap[j'].var.1, by omega⟩, rl, rh⟩ sh invh
                ⟨_, (hhp _).1 _ hl⟩
                ⟨_, hh⟩
                (by
                  simp only
                  rw [O_root_def, U_root_def]
                  simp only [Fin.getElem_fin, toVar_or]
                  have heeq : O.1.heap[j].var.1 = U.1.heap[j'].var.1 := by omega
                  simp only [Fin.getElem_fin] at heeq
                  rw [heeq]
                  simp only [min_self]
                )
                (by
                  intro j'' hj1
                  simp only [Fin.getElem_fin]
                  intro hj2
                  have := (hhp _).1 _ hl
                  simp only at this
                  rw [hj2] at this
                  have that := (invh.2 _ _ this).1 _ hj1 rfl
                  simp only at that
                  rw [that]
                  exact aux_lt5_low O_root_def U_root_def (by omega)
                )
                (by
                  intro j'' hj1
                  simp only [Fin.getElem_fin]
                  intro hj2
                  have := (invh.2 _ _ hh).1 _ hj1 hj2
                  rw [this]
                  exact aux_lt5_high O_root_def U_root_def (by omega)
                )
                (by
                  intro h0 h1 I
                  symm
                  rw [OBdd.evaluate_node'' U_root_def]
                  rw [OBdd.evaluate_node'' O_root_def]
                  simp only
                  have heeq : O.1.heap[j].var.1 = U.1.heap[j'].var.1 := by omega
                  have heo := Vector.getElem_extract (as := I) (start := 0) (stop := n) (i := O.1.heap[j.1].var.1) (by omega)
                  have heu := Vector.getElem_extract (as := I) (start := 0) (stop := n') (i := U.1.heap[j'.1].var.1) (by omega)
                  have : (Vector.cast (m := n') (by omega) (I.extract 0 n'))[U.1.heap[j'].var] = (Vector.cast (m := n) (by omega) (I.extract 0 n))[O.1.heap[j].var] := by
                    simp only [Fin.getElem_fin]
                    rw [Vector.getElem_cast]
                    rw [Vector.getElem_cast]
                    rw [heo]
                    rw [heu]
                    simp only [zero_add]
                    congr 1
                    symm
                    exact heeq
                  rw [this]
                  rw [op_if3 op]
                  simp only [OBdd.evaluate_node]
                  congr 1
                  ·
                    simp only [Nat.sub_zero, Fin.getElem_fin, Vector.getElem_cast, cook_heap,
                      RawNode.cook, Vector.getElem_ofFn, Vector.getElem_push_eq, eq_iff_iff,
                      Bool.coe_iff_coe]
                    simp only [zero_add] at heo
                    simp_all only [getElem?_eq_none_iff, OBdd.low_heap_eq_heap, forall_exists_index,
                      Prod.forall, OBdd.high_heap_eq_heap, Fin.getElem_fin, Nat.sub_zero, zero_add,
                      Vector.getElem_cast]
                  ·
                    conv =>
                      rhs
                      congr
                      congr
                      congr
                      rfl
                      simp [cook_heap, RawNode.cook]
                      rfl
                      rfl
                    symm
                    have h := invh.2 ⟨(O.high O_root_def).1.root, (U.high U_root_def).1.root⟩ rh hh
                    rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
                    refine Eq.trans ?_ (h6 I)
                    exact congrFun (push_evaluate (hq := h4) (hp := RawPointer.bounded_of_le h4 (by omega)) (h0 := h0) (ho := push_ordered h5) (hu := h5)) I
                  ·
                    conv =>
                      rhs
                      congr
                      congr
                      congr
                      rfl
                      simp [cook_heap, RawNode.cook]
                      rfl
                      rfl
                    symm
                    have : sh.cache[(⟨(O.low O_root_def).1.root, (U.low U_root_def).1.root⟩ : Pointer m × Pointer m')]? = some rl := by
                      apply (hhp _).1
                      exact hl
                    have h := invh.2 ⟨(O.low O_root_def).1.root, (U.low U_root_def).1.root⟩ rl this
                    rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
                    refine Eq.trans ?_ (h6 I)
                    exact congrFun (push_evaluate (hq := h4) (hp := RawPointer.bounded_of_le h4 (by omega)) (h0 := h0) (ho := push_ordered h5) (hu := h5)) I
                )
                (by
                  simp only [cache_get] at hc
                  cases heq : sh.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
                  | none => rfl
                  | some val =>
                    cases heqq : sl.cache[(⟨O.1.root, U.1.root⟩ : Pointer m × Pointer m')]? with
                    | none =>
                      have := ((hhp _).2.2 heqq ⟨val, heq⟩).2
                      simp only [OBdd.high_heap_eq_heap] at this
                      absurd this
                      apply OBdd.not_oedge_reachable
                      exact oedge_of_high
                    | some val =>
                      have := ((hlp _).2.2 hc ⟨_, heqq⟩).2
                      simp only [OBdd.low_heap_eq_heap] at this
                      absurd this
                      apply OBdd.not_oedge_reachable
                      exact oedge_of_low
                )
          ⟨ r,
            invv,
            (by rw [O_root_def, U_root_def] at hv; exact hv),
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
                  rw [← O_root_def, ← U_root_def]
                  cases heq : sh.cache[k]? with
                  | none =>
                    apply (hvp _).2.2 heq hkp
                  | some w =>
                    cases heqq : sl.cache[k]? with
                    | none =>
                      have := (hhp _).2.2 heqq ⟨_, heq⟩
                      constructor
                      · trans (O.high O_root_def).1.root
                        · apply OBdd.reachable_of_edge
                          exact oedge_of_high.2
                        · exact this.1
                      · trans (U.high U_root_def).1.root
                        · apply OBdd.reachable_of_edge
                          exact oedge_of_high.2
                        · exact this.2
                    | some ww =>
                      have := (hlp _).2.2 hk ⟨_, heqq⟩
                      constructor
                      · trans (O.low O_root_def).1.root
                        · apply OBdd.reachable_of_edge
                          exact oedge_of_low.2
                        · exact this.1
                      · trans (U.low U_root_def).1.root
                        · apply OBdd.reachable_of_edge
                          exact oedge_of_low.2
                        · exact this.2
          ⟩
termination_by (O, U)
decreasing_by
  · right; exact oedge_of_low
  · right; exact oedge_of_high
  · left;  exact oedge_of_low
  · left;  exact oedge_of_high
  · left;  exact oedge_of_low
  · left;  exact oedge_of_high
  · right; exact oedge_of_low
  · right; exact oedge_of_high
  · left; exact oedge_of_low
  · left; exact oedge_of_high
def oapply (op : Bool → Bool → Bool) (O : OBdd n m) (U : OBdd n' m') :
    (s : Nat) ×
    { OU : OBdd (n ⊔ n') s //
      ∀ I,
        OU.evaluate I =
        (op
          (O.evaluate (Vector.cast (by simp) (I.take n)))
          (U.evaluate (Vector.cast (by simp) (I.take n'))))
    } :=
  let ⟨⟨state, root⟩, inv, ps⟩ := apply_helper op O U initial inv_initial
  ⟨ state.size,
    ⟨⟨cook_heap state.heap inv.1,
    root.cook (inv.2 _ root ps.1).2.2.2.1⟩,
    (inv.2 _ root ps.1).2.2.2.2.1⟩,
    (inv.2 _ root ps.1).2.2.2.2.2
  ⟩
end Apply


