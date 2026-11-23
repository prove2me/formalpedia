-- Prove2me | Definitions.Def_Bdd_Count
-- name    : Bdd_Count
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T06:59:08.114177+00:00
-- url     : https://prove2.me/theorems/32c034d1-205b-4ebd-a60c-3a9b2e935d27
-- title:
--   Count
-- statement:
--   Definitions and structural lemmas for Count, from Eshel Yaron and contributors's pinned Correctness of binary decision diagrams for CNF formulas development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Count.lean

import Definitions.Def_Bdd_Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.BigOperators
import Std.Data.HashMap.Lemmas
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_OBdd_evaluate_high_eq_evaluate_set_true
import Theorems.Thm_OBdd_evaluate_low_eq_evaluate_set_false
import Theorems.Thm_OBdd_independentOf_lt_root
import Theorems.Thm_OBdd_var_lt_high_var
import Theorems.Thm_OBdd_var_lt_low_var
import Theorems.Thm_P2M_OBdd_evaluate_terminal__321343d95937
attribute [local simp] Nary.restrict_const


set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered
namespace Count
def Solution (O : OBdd n m) := { I : Vector Bool n // O.evaluate I = true}
lemma solution_iff_exists (O : OBdd n m) (i : Fin n) : O.evaluate I = true ↔ ∃ b, I[i] = b ∧ O.evaluate I = true := by simp
lemma solution_iff_or (O : OBdd n m) (i : Fin n) :
    (fun I ↦ O.evaluate I = true) = (fun I ↦ (I[i] = false ∧ O.evaluate I = true) ∨ (I[i] = true ∧ O.evaluate I = true)) := by
  ext I
  nth_rw 1 [solution_iff_exists O i]
  simp only [Bool.exists_bool]
def my_vector_equiv_vector : List.Vector α n ≃ Vector α n where
  toFun     := fun l ↦ ⟨l.toList.toArray, .trans List.size_toArray   (List.Vector.toList_length _)⟩
  invFun    := fun v ↦ ⟨v.toList,         .trans Array.length_toList (Vector.size_toArray       _)⟩
  left_inv  := fun x ↦ (by simp)
  right_inv := fun x ↦ (by simp; try rfl)
instance instVectorFintype [Fintype α] {n : ℕ} : Fintype (Vector α n) := Fintype.ofEquiv (List.Vector α n) my_vector_equiv_vector
@[simp]
lemma my_card_vector [Fintype α] (n : Nat) : Fintype.card (Vector α n) = Fintype.card α ^ n :=
  .trans (Fintype.ofEquiv_card my_vector_equiv_vector) (card_vector n)
instance instFintypeSolution {O : OBdd n m} : Fintype (Solution O) := Subtype.fintype _
abbrev numSolutions (O : OBdd n m) : Nat := Fintype.card (Solution O)
lemma numSolutions_terminal {O : OBdd n m} (h : O.1.root = .terminal b) :
    numSolutions O = if b then 2 ^ n else 0 := by
  have he := OBdd.evaluate_terminal' (O := O) h
  let e : Solution O ≃ {I : Vector Bool n // b = true} :=
    Equiv.subtypeEquivRight (fun I => by change O.evaluate I = true ↔ b = true; rw [he]; rfl)
  rw [numSolutions, Fintype.card_congr e]
  cases b <;> simp
lemma numSolutions_eq_card_or (O : OBdd n m) (i : Fin n) :
    numSolutions O = Fintype.card {I : Vector Bool n // (I[i] = false ∧ O.evaluate I = true) ∨ (I[i] = true ∧ O.evaluate I = true)} :=
  Fintype.card_congr (Equiv.subtypeEquivProp (solution_iff_or ..))
lemma card_solution_low (O : OBdd n m) (h : O.1.root = .node j):
    Fintype.card {I : Vector Bool n // I[O.1.heap[j].var] = false ∧ O.evaluate I = true} = Fintype.card {I : Vector Bool n // I[O.1.heap[j].var] = false ∧ (O.low h).evaluate I = true} :=
  Fintype.card_congr (Equiv.subtypeEquivProp (by
    ext I
    simp only [Fin.getElem_fin, and_congr_right_iff, Bool.coe_iff_coe]
    intro hf
    rw [OBdd.evaluate_low_eq_evaluate_set_false]
    simp only [Fin.getElem_fin, Function.comp_apply]
    congr
    rw [← hf]
    simp only [Vector.set_getElem_self]
  ))
lemma card_solution_high (O : OBdd n m) (h : O.1.root = .node j):
    Fintype.card {I : Vector Bool n // I[O.1.heap[j].var] = true ∧ O.evaluate I = true} = Fintype.card {I : Vector Bool n // I[O.1.heap[j].var] = true ∧ (O.high h).evaluate I = true} :=
  Fintype.card_congr (Equiv.subtypeEquivProp (by
    ext I
    simp only [Fin.getElem_fin, and_congr_right_iff, Bool.coe_iff_coe]
    intro hf
    rw [OBdd.evaluate_high_eq_evaluate_set_true]
    simp only [Fin.getElem_fin, Function.comp_apply]
    congr
    rw [← hf]
    simp only [Vector.set_getElem_self]
  ))
lemma aux {i : Fin n} {P Q : Vector Bool n → Prop}: Disjoint (fun I ↦ I[i] = false ∧ P I)  (fun I ↦ I[i] = true ∧ Q I) := by
  intro p hp1 hp2
  simp only [le_bot_iff]
  ext I
  simp only [Pi.bot_apply, «Prop».bot_eq_false, iff_false]
  intro contra
  have hI1 := hp1 I contra
  have hI2 := hp2 I contra
  simp_all
lemma aux_low {O : OBdd n m} {h : O.1.root = .node j}: (O.low h).evaluate (I.set (O.1.heap[j.1].var : Fin n) b) = (O.low h).evaluate I := by
  have : Nary.IndependentOf (O.low h).evaluate O.1.heap[j.1].var := by
    apply OBdd.independentOf_lt_root (O := (O.low h)) (i := ⟨O.1.heap[j.1].var.1, ?_⟩)
    have := OBdd.var_lt_low_var (O := O) (h := h)
    conv at this =>
      lhs
      simp [h, Pointer.toVar_node_eq]
    exact this
  simp_all
lemma aux_high {O : OBdd n m} {h : O.1.root = .node j}: (O.high h).evaluate (I.set (O.1.heap[j.1].var) b) = (O.high h).evaluate I := by
  have : Nary.IndependentOf (O.high h).evaluate O.1.heap[j.1].var := by
    apply OBdd.independentOf_lt_root (O := (O.high h)) (i := ⟨O.1.heap[j.1].var.1, ?_⟩)
    have := OBdd.var_lt_high_var (O := O) (h := h)
    conv at this =>
      lhs
      simp [h, Pointer.toVar_node_eq]
    exact this
  simp_all
lemma numSolutions_node {O : OBdd n m} {j : Fin m} (h : O.1.root = .node j) : numSolutions O + numSolutions O = numSolutions (O.low h) + numSolutions (O.high h) := by
  nth_rw 1 [numSolutions_eq_card_or O O.1.heap[j].var]
  rw [Fintype.card_subtype_or_disjoint _ _ aux]
  · rw [card_solution_low O h]
    rw [card_solution_high O h]
    nth_rw 1 [numSolutions_eq_card_or O O.1.heap[j].var]
    rw [Fintype.card_subtype_or_disjoint _ _ aux]
    · rw [card_solution_low O h]
      rw [card_solution_high O h]
      have h1 : Fintype.card { I // I[O.1.heap[j].var] = false ∧ (O.low h).evaluate I = true } = Fintype.card { I // I[O.1.heap[j].var] = true ∧ (O.low h).evaluate I = true } :=
        Fintype.card_congr
          { toFun := fun ⟨I, hI⟩ ↦ ⟨I.set O.1.heap[j].var true, by simp only [Fin.getElem_fin, Vector.getElem_set_self, true_and]; simp_all [aux_low]⟩
            invFun := fun ⟨I, hI⟩ ↦ ⟨I.set O.1.heap[j].var false, by simp only [Fin.getElem_fin, Vector.getElem_set_self, true_and]; simp_all [aux_low]⟩,
            left_inv := by rintro ⟨I, hI⟩; simp; rw [← hI.1]; simp
            right_inv := by rintro ⟨I, hI⟩; simp; rw [← hI.1]; simp
          }
      have h2 : Fintype.card { I // I[O.1.heap[j].var] = true ∧ (O.high h).evaluate I = true } = Fintype.card { I // I[O.1.heap[j].var] = false ∧ (O.high h).evaluate I = true } :=
        Fintype.card_congr
          { toFun := fun ⟨I, hI⟩ ↦ ⟨I.set O.1.heap[j].var false, by simp only [Fin.getElem_fin, Vector.getElem_set_self, true_and]; simp_all [aux_high]⟩
            invFun := fun ⟨I, hI⟩ ↦ ⟨I.set O.1.heap[j].var true, by simp only [Fin.getElem_fin, Vector.getElem_set_self, true_and]; simp_all [aux_high]⟩,
            left_inv := by rintro ⟨I, hI⟩; simp; rw [← hI.1]; simp
            right_inv := by rintro ⟨I, hI⟩; simp; rw [← hI.1]; simp
          }
      nth_rw 1 [h1]
      nth_rw 1 [h2]
      calc _
        _ = Fintype.card { I // I[O.1.heap[j].var] = false ∧ (O.low h).evaluate I = true } + Fintype.card { I // I[O.1.heap[j].var] = true ∧ (O.low h).evaluate I = true } +
            (Fintype.card { I // I[O.1.heap[j].var] = false ∧ (O.high h).evaluate I = true } + Fintype.card { I // I[O.1.heap[j].var] = true ∧ (O.high h).evaluate I = true }) := by omega
      rw [← Fintype.card_subtype_or_disjoint _ _ aux]
      rw [← Fintype.card_subtype_or_disjoint _ _ aux]
      rw [← numSolutions_eq_card_or _ O.1.heap[j].var]
      rw [← numSolutions_eq_card_or _ O.1.heap[j].var]
def Invariant (O : OBdd n m) (s : Std.HashMap (Pointer m) Nat) :=
  ∀ p (hp : p ∈ s),
    ∃ ho : Bdd.Ordered ⟨O.1.heap, p⟩,
      s[p]'hp = numSolutions ⟨⟨O.1.heap, p⟩, ho⟩
def PostCond (O : OBdd n m) (s r : Std.HashMap (Pointer m) Nat) :=
  (∀ p,
    (∀ i, s[p]? = some i → r[p]? = some i) ∧
    (r[p]? = none → s[p]? = none) ∧
    (s[p]? = none → (∃ i, r[p]? = some i) → Pointer.Reachable O.1.heap O.1.root p))
instance postCond_refl : Std.Refl (PostCond O) where
  refl := by
    intro _ _
    grind only
lemma postCond_terminal (hr : s[O.1.root]? = none) (h : O.1.root = Pointer.terminal b) :
    PostCond O s (s.insert (Pointer.terminal b) i) := by
  intro p
  constructor
  · intro i hi
    simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
    split
    next heq =>
      subst heq
      simp_all
    next => exact hi
  · constructor
    · simp_all
    · intro hp1 ⟨_, hp2⟩
      simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at hp2
      split at hp2
      next heq =>
        injection hp2 with hpi
        subst hpi
        subst heq
        rw [h]
        left
      next => simp_all
lemma invariant_false (O : OBdd n m) (s : Std.HashMap (Pointer m) Nat ) (inv : Invariant O s) :
    Invariant O (s.insert (Pointer.terminal false) 0) := by
  intro p hp
  simp only [Std.HashMap.mem_insert, beq_iff_eq] at hp
  cases hp with
  | inl hp =>
    subst hp
    refine ⟨Bdd.Ordered_of_terminal, ?_⟩
    rw [Std.HashMap.getElem_insert_self, numSolutions_terminal rfl]
    rfl
  | inr hp =>
    obtain ⟨ha, hb⟩ := inv p hp
    use ha
    rw [Std.HashMap.getElem_insert]
    simp only [beq_iff_eq]
    split
    next heq => subst heq; rw [numSolutions_terminal rfl]; rfl
    next => exact hb
lemma invariant_true (O : OBdd n m) (s : Std.HashMap (Pointer m) Nat ) (inv : Invariant O s) :
    Invariant O (s.insert (Pointer.terminal true) (2 ^ n)) := by
  intro p hp
  simp only [Std.HashMap.mem_insert, beq_iff_eq] at hp
  cases hp with
  | inl hp =>
    subst hp
    refine ⟨Bdd.Ordered_of_terminal, ?_⟩
    rw [Std.HashMap.getElem_insert_self, numSolutions_terminal rfl]
    rfl
  | inr hp =>
    obtain ⟨ha, hb⟩ := inv p hp
    use ha
    rw [Std.HashMap.getElem_insert]
    simp only [beq_iff_eq]
    split
    next heq => subst heq; rw [numSolutions_terminal rfl]; rfl
    next => exact hb
lemma invariant_node (O : OBdd n m) (s : Std.HashMap (Pointer m) Nat ) (inv : Invariant O s) (h : O.1.root = Pointer.node j) :
    Invariant O (s.insert (Pointer.node j) (((numSolutions (O.low h)) + (numSolutions (O.high h))) / 2)) := by
  intro p hp
  simp only [Std.HashMap.mem_insert, beq_iff_eq] at hp
  cases hp with
  | inl hp =>
    subst hp
    simp_rw [← h]
    use O.2
    simp only [Std.HashMap.getElem_insert_self]
    symm
    apply Nat.eq_div_of_mul_eq_left
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    · rw [mul_two]
      exact numSolutions_node h
  | inr hp =>
    obtain ⟨ha, hb⟩ := inv p hp
    use ha
    rw [Std.HashMap.getElem_insert]
    simp only [beq_iff_eq]
    split
    next heq =>
      subst heq
      simp_rw [← h]
      symm
      apply Nat.eq_div_of_mul_eq_left
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
      · rw [mul_two]
        exact numSolutions_node h
    next => exact hb
def count_helper (O : OBdd n m) (s : Std.HashMap (Pointer m) Nat ) (inv : Invariant O s) :
    { r : Std.HashMap (Pointer m) Nat //
      Invariant O r ∧
      O.1.root ∈ r ∧
      PostCond O s r
    } :=
  match hr : s[O.1.root]? with
  | some i => ⟨s, inv, by apply Std.HashMap.isSome_getElem?_iff_mem.mp; simp_all only [Option.isSome_some], refl s⟩
  | none =>
    match h : O.1.root with
    | .terminal false => ⟨s.insert (.terminal false) 0, invariant_false O s inv, by simp only [Std.HashMap.mem_insert, BEq.rfl, true_or], postCond_terminal hr h⟩
    | .terminal true => ⟨s.insert (.terminal true) (2 ^ n), invariant_true O s inv, by simp only [Std.HashMap.mem_insert, BEq.rfl, true_or], postCond_terminal hr h⟩
    | .node j =>
      let ⟨sl, invl, hl1, hl2⟩ := count_helper (O.low h) s inv
      let ⟨sh, invh, hh1, hh2⟩ := count_helper (O.high h) sl invl
      have hlh : (O.low h).1.root ∈ sh := by
        apply Std.HashMap.mem_iff_isSome_getElem?.mp at hl1
        apply Option.eq_some_of_isSome at hl1
        have := (hh2 _).1 _ hl1
        apply Std.HashMap.mem_iff_isSome_getElem?.mpr
        apply Option.isSome_of_eq_some
        exact this
      ⟨ sh.insert (.node j) ((sh[(O.low h).1.root]'hlh + sh[(O.high h).1.root]'hh1) / 2), (by rw [(invh _ hh1).2]; rw [(invh _ hlh).2]; exact invariant_node O sh invh h), by simp only [Std.HashMap.mem_insert, BEq.rfl, true_or], by
          intro p
          constructor
          · intro i hpi
            simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
            split
            next heq =>
              subst heq
              simp_all
            next =>
              exact (hh2 _).1 _ ((hl2 _).1 _ hpi)
          · constructor
            · intro hn
              simp only [getElem?_eq_none_iff, Std.HashMap.mem_insert, beq_iff_eq, not_or] at hn
              rcases hn with ⟨hn1, hn2⟩
              rw [← getElem?_eq_none_iff] at hn2
              exact (hl2 _).2.1 ((hh2 _).2.1 hn2)
            · intro hp1 ⟨_, hp2⟩
              simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at hp2
              split at hp2
              next heq =>
                injection hp2 with hpi
                subst hpi
                subst heq
                rw [h]
                left
              next i _ =>
                cases hm : sl[p]? with
                | none =>
                  trans (O.high h).1.root
                  · right
                    rfl
                    simp only [h, OBdd.high, Bdd.high, Fin.getElem_fin]
                    right
                    rfl
                  · exact (hh2 _).2.2 hm ⟨_, hp2⟩
                | some val =>
                  trans (O.low h).1.root
                  · right
                    rfl
                    simp only [h, OBdd.low, Bdd.low, Fin.getElem_fin]
                    left
                    rfl
                  · exact (hl2 _).2.2 hp1 ⟨_, hm⟩
      ⟩
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
def count (O : OBdd n m) : Nat :=
  let ⟨r, _, hin, _⟩ := count_helper O (Std.HashMap.emptyWithCapacity) (by simp [Invariant])
  r[O.1.root]'hin
end Count


