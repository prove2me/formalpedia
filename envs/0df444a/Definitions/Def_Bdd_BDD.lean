-- Prove2me | Definitions.Def_Bdd_BDD
-- name    : Bdd_BDD
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:19:13.268044+00:00
-- url     : https://prove2.me/theorems/8a57536a-8d30-4c6f-b24a-62543138e7ba
-- title:
--   BDD
-- statement:
--   Definitions and structural lemmas for BDD, from Eshel Yaron and contributors's pinned Correctness of binary decision diagrams for CNF formulas development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/BDD.lean

import Definitions.Def_Bdd_Reduce
import Definitions.Def_Bdd_Apply
import Definitions.Def_Bdd_Relabel
import Definitions.Def_Bdd_Choice
import Definitions.Def_Bdd_Restrict
import Definitions.Def_Bdd_Evaluate
import Definitions.Def_Bdd_Sim
import Definitions.Def_Bdd_Size
import Definitions.Def_Bdd_Count
import Theorems.Thm_Bdd_ordered_of_low_high_ordered
import Theorems.Thm_Bdd_reduced_of_terminal
import Theorems.Thm_Evaluate_evaluate_evaluate
import Theorems.Thm_Evaluate_evaluate_node
import Theorems.Thm_Evaluate_evaluate_terminal
import Theorems.Thm_Lift_olift_evaluate
import Theorems.Thm_Lift_olift_olift
import Theorems.Thm_Lift_olift_reduced
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_Nary_restrict_eq_self_of_independentOf
import Theorems.Thm_OBdd_Canonicity
import Theorems.Thm_OBdd_Canonicity_reverse
import Theorems.Thm_OBdd_reduced_of_terminal
import Theorems.Thm_OBdd_usesVar_iff_dependsOn_of_reduced
import Theorems.Thm_Pointer_Reachable_iff
import Theorems.Thm_Reduce_oreduce_evaluate
import Theorems.Thm_Relabel_orelabel_id
import Theorems.Thm_Relabel_orelabel_reduced
attribute [local simp] Lift.olift_evaluate
attribute [local simp] Lift.olift_olift
attribute [local simp] Nary.restrict_const
attribute [local simp] Reduce.oreduce_evaluate
attribute [local simp] Relabel.orelabel_id


set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered Lift.olift Relabel.orelabel Reduce.oreduce
structure BDD where
  /-- BDD input size (number of variables). -/
  nvars         : Nat
  private nheap : Nat
  private obdd  : OBdd nvars nheap
  private hred  : obdd.Reduced
namespace BDD
@[simp]
abbrev evaluate (B : BDD) : Vector Bool B.nvars → Bool := Evaluate.evaluate B.obdd
def lift (B : BDD) (h : B.nvars ≤ n) : BDD :=
  ⟨n, _, Lift.olift h B.obdd, Lift.olift_reduced B.hred⟩
@[simp]
lemma lift_nvars {B : BDD} {h : B.nvars ≤ n} : (B.lift h).nvars = n := rfl
@[simp]
lemma lift_refl {B : BDD} : (B.lift (le_refl _)) = B := by simp [lift]
attribute [local implicit_reducible] lift
def denotation (B : BDD) (h : B.nvars ≤ n) : Vector Bool n → Bool := (B.lift h).evaluate
attribute [local implicit_reducible] denotation
@[simp]
abbrev denotation' O := denotation O (le_refl _)
@[simp]
lemma lift_denotation {B : BDD} {h1 : B.nvars ≤ n} {h2 : n ≤ m} :
    (B.lift h1).denotation h2 = B.denotation (.trans h1 h2) := by
  simp [denotation, lift, Evaluate.evaluate_evaluate]
@[simp]
lemma denotation_cast {B : BDD} {hn : B.nvars ≤ n} {hm : B.nvars ≤ m} (h : n = m) :
    B.denotation hm (Vector.cast h I) = B.denotation hn I := by
  subst h
  simp
lemma denotation_independentOf_of_geq_nvars {n : Nat} {i : Fin n} {B : BDD} {h1 : B.nvars ≤ n} {h2 : B.nvars ≤ i} :
    Nary.IndependentOf (B.denotation h1) i := by
  rintro b I
  simp only [denotation, Evaluate.evaluate_evaluate, Lift.olift_evaluate, lift]
  suffices s : (I.set i b).take B.nvars = I.take B.nvars by rw [s]
  ext j hj
  simp only [Vector.getElem_take]
  rw [Vector.getElem_set_ne _ _ (by omega)]
def SemanticEquiv (B C : BDD) := B.denotation (le_max_left ..) = C.denotation (le_max_right ..)
def Similar (B : BDD) (B' : BDD) :=
  (Lift.olift (Nat.le_max_left ..) B.obdd).HSimilar (Lift.olift (Nat.le_max_right ..) B'.obdd)
lemma denotation_take {B : BDD} {hn : B.nvars ≤ n} {hm1 : B.nvars ≤ m} {hm2 : m ≤ n}:
    B.denotation hn I = B.denotation (by simp_all) (I.take m) := by
  simp [denotation, Evaluate.evaluate_evaluate, lift]
  congr!
  omega
lemma denotation_take' {B : BDD} {hn : B.nvars ≤ n} :
    B.denotation hn I = B.denotation (le_refl _) (Vector.cast (by simp_all) (I.take B.nvars)) := by
  simp [denotation, Evaluate.evaluate_evaluate, lift]
instance instDecidableSimilar : DecidableRel Similar
  | B, C =>
    Sim.instDecidableRobddHSimilar
      (Lift.olift (Nat.le_max_left  ..) B.obdd) (Lift.olift_reduced B.hred)
      (Lift.olift (Nat.le_max_right ..) C.obdd) (Lift.olift_reduced C.hred)
theorem SemanticEquiv_iff_Similar {B C : BDD} :
    B.SemanticEquiv C ↔ B.Similar C := ⟨l_to_r, r_to_l⟩ where
  l_to_r h := by
    simp [Evaluate.evaluate_evaluate, SemanticEquiv, denotation] at h
    exact OBdd.Canonicity (Lift.olift_reduced B.hred) (Lift.olift_reduced C.hred) h
  r_to_l h := by
    simp [SemanticEquiv, denotation, Evaluate.evaluate_evaluate]
    exact OBdd.Canonicity_reverse h
instance instDecidableSemanticEquiv : DecidableRel SemanticEquiv
  | _, _ => decidable_of_iff' _ SemanticEquiv_iff_Similar
def size : BDD → Nat
  | B => Size.size B.obdd
def zero_vars_to_bool (B : BDD) : B.nvars = 0 → Bool := fun h ↦
  match B.obdd.1.root with
  | .terminal b => b
  | .node j => False.elim (Nat.not_lt_zero _ (Eq.subst h B.obdd.1.heap[j].var.2))
def const (b : Bool) : BDD :=
  { nvars := 0,
    nheap := 0,
    obdd  := ⟨⟨Vector.emptyWithCapacity 0, .terminal b⟩, Bdd.Ordered_of_terminal⟩,
    hred  := Bdd.reduced_of_terminal
  }
abbrev var_raw (n : Nat) : Bdd (n+1) 1 := ⟨Vector.singleton ⟨⟨n, Nat.lt_add_one n⟩, .terminal false, .terminal true⟩, .node 0⟩
lemma var_ordered : Bdd.Ordered (var_raw n) := by
  apply Bdd.ordered_of_low_high_ordered rfl
  · simp only [Bdd.low]
    conv =>
      congr
      right
      rw [Vector.singleton_def]
      simp [Vector.getElem_singleton (show 0 < 1 by omega)]
    apply Bdd.Ordered_of_terminal
  · simp [Bdd.low]
    apply Fin.lt_def.mpr
    refine Nat.lt_succ_of_le ?_
    simp [Pointer.toVar]
  · simp only [Bdd.high]
    conv =>
      congr
      right
      rw [Vector.singleton_def]
      simp [Vector.getElem_singleton (show 0 < 1 by omega)]
    apply Bdd.Ordered_of_terminal
  · simp [Bdd.high]
    apply Fin.lt_def.mpr
    refine Nat.lt_succ_of_le ?_
    simp [Pointer.toVar]
lemma var_reduced : OBdd.Reduced ⟨(var_raw n), var_ordered⟩ := by
  constructor
  · rintro ⟨p, hp⟩
    simp only [Fin.isValue] at hp
    rintro ⟨contra⟩
    simp_all
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [InvImage]
    simp only [OBdd.SimilarRP] at hxy
    cases Pointer.Reachable_iff.mp hx with
    | inl hh =>
      simp at hh
      cases Pointer.Reachable_iff.mp hy with
      | inl hhh =>
        simp only at hhh
        simp_rw [← hh, hhh]
      | inr hhh =>
        rcases hhh with ⟨j, hj, hhh⟩
        simp only at hj
        injection hj with hj
        simp only at hhh
        rw [← hj] at hhh
        simp at hhh
        rcases hhh with hhh | hhh <;>
        apply Pointer.eq_terminal_of_reachable at hhh <;>
        simp_rw [← hh, hhh] at hxy <;>
        simp only [OBdd.Similar, OBdd.HSimilar] at hxy <;>
        unfold OBdd.toTree at hxy <;>
        simp at hxy
    | inr hh =>
      simp only at hh
      rcases hh with ⟨j, hj, hh⟩
      injection hj with hj
      rw [← hj] at hh
      simp at hh
      cases Pointer.Reachable_iff.mp hy with
      | inl hhh =>
        simp only at hhh
        rcases hh with hh | hh <;>
        apply Pointer.eq_terminal_of_reachable at hh <;>
        simp_rw [hh, ← hhh] at hxy <;>
        simp only [OBdd.Similar, OBdd.HSimilar] at hxy <;>
        unfold OBdd.toTree at hxy <;>
        simp at hxy
      | inr hhh =>
        simp only at hhh
        rcases hhh with ⟨i, hi, hhh⟩
        injection hi with hi
        rw [← hi] at hhh
        simp at hhh
        cases hh with
        | inl hh =>
          apply Pointer.eq_terminal_of_reachable at hh
          cases hhh with
          | inl hhh =>
            apply Pointer.eq_terminal_of_reachable at hhh
            simp_all
          | inr hhh =>
            apply Pointer.eq_terminal_of_reachable at hhh
            simp_rw [hh, hhh] at hxy
            simp [OBdd.Similar, OBdd.HSimilar] at hxy
        | inr hh =>
          cases hhh with
          | inl hhh =>
            apply Pointer.eq_terminal_of_reachable at hh
            apply Pointer.eq_terminal_of_reachable at hhh
            simp_rw [hh, hhh] at hxy
            simp only [OBdd.Similar, OBdd.HSimilar] at hxy
            unfold OBdd.toTree at hxy
            simp at hxy
          | inr hhh =>
            apply Pointer.eq_terminal_of_reachable at hh
            apply Pointer.eq_terminal_of_reachable at hhh
            rw [hh, hhh]
def var (n : Nat) : BDD :=
  { nvars := n + 1,
    nheap := 1,
    obdd  := ⟨⟨Vector.singleton ⟨⟨n, Nat.lt_add_one n⟩, .terminal false, .terminal true⟩, .node 0⟩, var_ordered⟩,
    hred  := var_reduced
  }
def apply : (Bool → Bool → Bool) → BDD → BDD → BDD := fun op B C ↦
  let r := Reduce.oreduce (Apply.oapply op B.obdd C.obdd).2.1
  ⟨_, _, r.1.2, r.2.1⟩
@[simp]
lemma apply_nvars {B C : BDD} {o} : (apply o B C).nvars = B.nvars ⊔ C.nvars := by
  simp only [apply]
def and : BDD → BDD → BDD := apply Bool.and
def or  : BDD → BDD → BDD := apply Bool.or
def xor : BDD → BDD → BDD := apply Bool.xor
def imp : BDD → BDD → BDD := apply (! · || ·)
def not : BDD → BDD       := fun B ↦ imp B (const false)
attribute [local implicit_reducible] const var apply
@[simp]

lemma const_nvars : (const b).nvars = 0 := rfl
@[simp]
lemma const_denotation : (const b).denotation h = Function.const _ b := by
  apply Evaluate.evaluate_terminal
  rfl
@[simp]
lemma var_nvars : (var i).nvars = i + 1 := rfl
@[simp]
lemma var_denotation {n i h1} {h2 : i < n} {I : Vector Bool n} :
    (var i).denotation h1 I = I[i]'h2 := by
  simp +instances [denotation, evaluate, var, lift, Evaluate.evaluate_evaluate, Lift.olift_evaluate]
  have : (I.take (i + 1))[i] = I[i] := by
    apply Vector.getElem_take
  erw [← this]
  rw [← Evaluate.evaluate_evaluate]
  rw [Evaluate.evaluate_node (by rfl)]
  dsimp only
  split <;> simp_all
  all_goals exact congrFun (Evaluate.evaluate_terminal (by rfl)) _
lemma apply_denotation' {B C : BDD} {op} I :
    (apply op B C).denotation (le_refl _) I =
    (op (B.denotation (by simp_all) I) (C.denotation (by simp_all) I)) := by
  unfold apply
  generalize he : (apply op B C) = e
  unfold apply at he
  simp +instances only [denotation, Evaluate.evaluate_evaluate, lift, Lift.olift_evaluate, Reduce.oreduce_evaluate]
  calc _
    _ = (Apply.oapply op (BDD.obdd B) (BDD.obdd C)).2.1.evaluate I := by simp
  exact (Apply.oapply op (BDD.obdd B) (BDD.obdd C)).2.2 I
@[simp]
lemma apply_denotation {B C : BDD} {op} {I : Vector Bool n} {h} :
    (apply op B C).denotation h I =
    (op (B.denotation (by simp_all) I) (C.denotation (by simp_all) I)) := by
  rw [denotation_take']
  rw [apply_denotation']
  congr 1
  rw [denotation_cast (I := (I.take (apply op B C).nvars))]
  · nth_rw 2 [denotation_take] <;> simp_all
  · rw [denotation_cast]
    nth_rw 2 [denotation_take] <;> simp_all
@[simp]
lemma and_nvars {B C : BDD} : (B.and C).nvars = B.nvars ⊔ C.nvars := apply_nvars
@[simp]
lemma and_denotation {B C : BDD} {I : Vector Bool n} {h} :
    (B.and C).denotation h I = ((B.denotation (by simp_all) I) && (C.denotation (by simp_all) I)) := apply_denotation
@[simp]
lemma or_nvars {B C : BDD} : (B.or C).nvars = B.nvars ⊔ C.nvars := apply_nvars
@[simp]
lemma or_denotation {B C : BDD} {I : Vector Bool n} {h} :
    (B.or C).denotation h I = ((B.denotation (by simp_all) I) || (C.denotation (by simp_all) I)) := apply_denotation
@[simp]
lemma xor_nvars {B C : BDD} : (B.xor C).nvars = B.nvars ⊔ C.nvars := apply_nvars
@[simp]
lemma xor_denotation {B C : BDD} {I : Vector Bool n} {h} :
    (B.xor C).denotation h I = ((B.denotation (by simp_all) I) ^^ (C.denotation (by simp_all) I)) := apply_denotation
@[simp]
lemma imp_nvars {B C : BDD} : (B.imp C).nvars = B.nvars ⊔ C.nvars := apply_nvars
@[simp]
lemma imp_denotation {B C : BDD} {I : Vector Bool n} {h} :
    (B.imp C).denotation h I = (!(B.denotation (by simp_all) I) || (C.denotation (by simp_all) I)) := apply_denotation
@[simp]
lemma not_nvars {B : BDD} : B.not.nvars = B.nvars := by
  simp only [not, imp, apply_nvars, const_nvars, zero_le, sup_of_le_left]
@[simp]
lemma not_denotation {B : BDD} {I : Vector Bool n} {h} :
    B.not.denotation h I = ! B.denotation (by simp_all) I := by simp [not]
def relabel' (B : BDD) (f : Nat → Nat)
      (h1 : ∀ i : Fin B.nvars, f i < f B.nvars)
      (h2 : ∀ i i', i < i' → Nary.DependsOn B.denotation' i → Nary.DependsOn B.denotation' i' → f i < f i') :
    BDD :=
  ⟨ f B.nvars, _,
    Relabel.orelabel B.obdd h1 (by
      intro i i' hii' hi hi'
      rw [OBdd.usesVar_iff_dependsOn_of_reduced B.hred] at hi
      rw [OBdd.usesVar_iff_dependsOn_of_reduced B.hred] at hi'
      simp only [denotation, Evaluate.evaluate_evaluate, Lift.olift_trivial_eq, lift] at h2
      exact h2 i i' hii' hi hi'),
    Relabel.orelabel_reduced B.hred
  ⟩
def relabel'' (B : BDD) (f : Nat → Nat)
      (h1 : ∀ i : Fin B.nvars, f i < f B.nvars)
      (h2 : ∀ i i' : (Nary.Dependency B.denotation'), i.1 < i'.1 → f i.1 < f i'.1) :
    BDD :=
  relabel' B f h1 (fun i i' hii' hi hi' ↦ h2 ⟨i, hi⟩ ⟨i', hi'⟩ hii')
def relabel_wrap (m n : Nat) (f : Fin m → Fin n) : Nat → Nat :=
  fun i ↦ if h : i < m then f ⟨i, h⟩ else n
@[simp]
lemma relabel_helper_aux : relabel_wrap m n f m = n := by
  simp [relabel_wrap]
@[simp]
lemma relabel_helper_aux' {i : Fin m} : relabel_wrap m n f i.1 = f i := by
  simp [relabel_wrap]
def relabel (B : BDD) (f : Fin B.nvars → Fin n)
    (h : ∀ i i' : (Nary.Dependency B.denotation'), i.1 < i'.1 → f i.1 < f i'.1) :
  BDD := relabel'' B (relabel_wrap B.nvars n f) (by simp) (fun i i' h' ↦ by simp [h i i' h'])
@[simp]
lemma relabel_nvars {B : BDD} {f : _ → Fin n} {h} : (relabel B f h).nvars = n := by
  simp [relabel, relabel'', relabel']
attribute [local implicit_reducible] relabel'' relabel'
lemma relabel_spec {B : BDD} {f : Nat → Nat} {hf} {hu} {I} :
    (relabel'' B f hf hu).denotation (le_refl _) I = B.denotation' (Vector.ofFn (fun i ↦ I[f i]'(hf i))) := by
  simp +instances [denotation, Evaluate.evaluate_evaluate, relabel'', relabel', lift]
@[simp]
lemma relabel''_denotation {B : BDD} {f : Nat → Nat} {hf} {hu} {I : Vector Bool n} {h} :
    (relabel'' B f hf hu).denotation h I =
    B.denotation' (Vector.ofFn (fun i ↦ I[f i]'(lt_of_lt_of_le (hf i) h))) := by
  rw [denotation_take']
  rw [relabel_spec]
  simp only [denotation']
  congr
  ext i
  simp only [Vector.getElem_cast]
  apply Vector.getElem_take
@[simp]
lemma relabel_denotation {B : BDD} {f} {hf} {I : Vector Bool n} {h} :
    (relabel B f hf).denotation h I = B.denotation' (Vector.ofFn (fun i ↦ I[f i])) := by
  simp [relabel]
def choice {B : BDD} (s : ∃ I, B.denotation' I) : Vector Bool B.nvars :=
  Choice.choice B.obdd (by simp_all [denotation, Evaluate.evaluate_evaluate, lift])
@[simp]
lemma choice_denotation {B : BDD} {s : ∃ I, B.denotation' I} : B.denotation' (B.choice s) = true := by
  simp [choice, denotation, lift, Evaluate.evaluate_evaluate, Choice.choice_evaluate B.hred (by simp_all [denotation, Evaluate.evaluate_evaluate, lift])]
lemma find_aux' {B : BDD} :
    ¬ B.SemanticEquiv (const false) → ∃ (I : Vector Bool (max B.nvars 0)), B.denotation (by simp) I := by
  intro h
  contrapose h
  simp_all +instances only [not_exists, Bool.not_eq_true, SemanticEquiv, const_nvars, const_denotation]
  ext x
  simp only [Function.const_apply]
  apply h
lemma find_aux {B : BDD} :
    ¬ B.SemanticEquiv (const false) → ∃ (I : Vector Bool B.nvars), B.denotation' I := by
  intro h
  rcases find_aux' h with ⟨I, hI⟩
  use ((show (max B.nvars 0) = B.nvars by simp) ▸ I)
  rw [← hI]
  clear hI
  congr! <;> simp
def find {B : BDD} : Option (Vector Bool B.nvars) :=
  if h : B.SemanticEquiv (const false) then none else some (choice (find_aux h))
def restrict' (B : BDD) (b : Bool) (i : Fin B.nvars) : BDD :=
  let r := Reduce.oreduce (Restrict.orestrict b i B.obdd).2.1
  ⟨_, _, r.1.2, r.2.1⟩
def restrict (b : Bool) (i : Nat) (B : BDD) : BDD :=
  if h : i < B.nvars
  then restrict' B b ⟨i, h⟩
  else B
attribute [local implicit_reducible] restrict restrict'
@[simp]
lemma restrict_nvars {B : BDD} {i} : (B.restrict b i).nvars = B.nvars := by
  simp only [restrict, restrict']
  split <;> simp
@[simp]
lemma Vector.cast_set {v : Vector α n} {i : Fin m} :
  (Vector.cast h v).set i a = Vector.cast h (v.set i a) := by rfl
@[simp]
lemma restrict_denotation {B : BDD} {I : Vector Bool n} {i} {hi : i < n} {h} :
    (B.restrict b i).denotation h I =
    (Nary.restrict (B.denotation (restrict_nvars ▸ h)) b ⟨i, hi⟩) I := by
  simp only [restrict]
  split
  next hlt =>
    simp +instances only [restrict', denotation, lift, evaluate, Evaluate.evaluate_evaluate, Lift.olift_evaluate]
    simp only [Reduce.oreduce_evaluate]
    have := (Restrict.orestrict b ⟨i, hlt⟩ (BDD.obdd B)).2.2
    rw [this]
    simp only [Nary.restrict, Vector.take_eq_extract, Lift.olift_evaluate]
    congr
    ext j hj
    simp
    rw [Vector.getElem_set]
    split
    next heq =>
      subst heq
      have := Vector.getElem_extract (as := I.set i b) (start := 0) (stop := B.nvars) (i := i) (by omega)
      simp_all
    next heq =>
      simp only [restrict_nvars] at h
      have := Vector.getElem_extract (as := I.set i b) (start := 0) (stop := B.nvars) (i := j) (by omega)
      have := Vector.getElem_extract (as := I) (start := 0) (stop := B.nvars) (i := j) (by omega)
      simp_all
  next hlt =>
    have := denotation_independentOf_of_geq_nvars (B := B) (h1 := restrict_nvars ▸ h) (h2 := (by simp_all)) (i := ⟨i, hi⟩)
    rw [Nary.restrict_eq_self_of_independentOf this]
instance instDecidableDependsOn (B : BDD) : DecidablePred (Nary.DependsOn B.denotation') := fun i ↦
  (show B.denotation' = B.obdd.evaluate by simp [denotation, Evaluate.evaluate_evaluate, lift]) ▸
  (decidable_of_iff _ (OBdd.usesVar_iff_dependsOn_of_reduced B.hred))
def bforall (B : BDD) (i : Nat) : BDD := (and (B.restrict false i) (B.restrict true i))
def bforalls (B : BDD) (l : List Nat) := List.foldl bforall B l
@[simp]
lemma bforall_nvars {B : BDD} {i} : (B.bforall i).nvars = B.nvars := by simp [bforall]
@[simp]
lemma bforall_denotation {B : BDD} {i} {hi : i < n} {I : Vector Bool n} {h} :
    (B.bforall i).denotation h I = (∀ b, B.denotation (by simp_all) (I.set i b) : Bool) := by simp_all [bforall]
@[simp]
lemma bforall_idem {B : BDD} {i} {hi : i < n} {I : Vector Bool n} {h} :
    ((B.bforall i).bforall i).denotation h I = (B.bforall i).denotation (by simp_all) I := by
  repeat (rw [bforall_denotation (hi := hi)]; simp_all)
def bexists (B : BDD) (i : Nat) : BDD := (or (B.restrict false i) (B.restrict true i))
def bexistss (B : BDD) (l : List Nat) := List.foldl bexists B l
@[simp]
lemma bexists_nvars {B : BDD} {i} : (B.bexists i).nvars = B.nvars := by simp [bexists]
@[simp]
lemma bexists_denotation {B : BDD} {i} {hi : i < n} {I : Vector Bool n} {h} :
    (B.bexists i).denotation h I = ((∃ b, B.denotation (by simp_all) (I.set i b)) : Bool) := by simp_all [bexists]
@[simp]
lemma bexists_idem {B : BDD} {i} {hi : i < n} {I : Vector Bool n} {h} :
    ((B.bexists i).bexists i).denotation h I = (B.bexists i).denotation (by simp_all) I := by
  repeat (rw [bexists_denotation (hi := hi)]; simp_all)
def count (B : BDD) : Nat := Count.count B.obdd
end BDD


