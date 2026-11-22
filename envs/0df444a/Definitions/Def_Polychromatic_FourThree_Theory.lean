-- Prove2me | Definitions.Def_Polychromatic_FourThree_Theory
-- name    : Polychromatic_FourThree_Theory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:46:31.120227+00:00
-- url     : https://prove2.me/theorems/9daee828-ef33-4ecf-8faa-511aeb5fbeac
-- title:
--   Theory
-- statement:
--   Definitions and structural lemmas for Theory, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Theory.lean

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_HasPolychromColouring_of_image
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ
attribute [local simp] polychromNumber_pair
attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ


set_option autoImplicit true
open Finset
section
def Accept (a b c : ℕ) : Prop :=
  HasPolychromColouring (Fin 3) {0, (a : ℤ), (b : ℤ), (c : ℤ)}
def allA (A : ℕ) (b c : ℕ) : Prop :=
  ∀ a : ℕ, 0 < a → a < b → a < A → a + b ≤ c → Nat.gcd a (Nat.gcd b c) = 1 → Accept a b c
def allB (B : ℕ) (c : ℕ) : Prop := ∀ b : ℕ, b < B → b < c → allA b b c
def allC (C : ℕ) : Prop := ∀ c : ℕ, c < C → allB c c
end
abbrev ModAccept (q aq bq cq : ℕ) : Prop :=
  ∀ a b c : ℕ, (a.mod q).beq aq → (b.mod q).beq bq → (c.mod q).beq cq → Accept a b c
def toBitVector (a b c : ℕ) : ℕ :=
  1 ||| 1 <<< a ||| 1 <<< b ||| 1 <<< c
def toBitVectorK (a b c : ℕ) : ℕ :=
  Nat.lor (Nat.lor (Nat.lor (nat_lit 1) (Nat.shiftLeft (nat_lit 1) a))
    (Nat.shiftLeft (nat_lit 1) b)) (Nat.shiftLeft (nat_lit 1) c)
def toDoubleBitVector (q a b c : ℕ) : ℕ :=
  toBitVector a b c ||| (toBitVector a b c <<< q)
def toDoubleBitVectorK (q a b c : ℕ) : ℕ :=
  Nat.lor (toBitVectorK a b c) (Nat.shiftLeft (toBitVectorK a b c) q)
lemma toBitVectorK_eq (a b c : ℕ) : toBitVectorK a b c = toBitVector a b c := rfl
@[simp] lemma toDoubleBitVectorK_eq (q a b c : ℕ) :
    toDoubleBitVectorK q a b c = toDoubleBitVector q a b c := rfl
lemma testBit_toBitVector (a b c i : ℕ) :
    Nat.testBit (toBitVector a b c) i = true ↔ i = 0 ∨ i = a ∨ i = b ∨ i = c := by
  rw [toBitVector]
  grind [Nat.testBit_one_eq_true_iff_self_eq_zero]
theorem Nat.shiftLeft_shiftRight_eq_shiftLeft_of_le {b c : Nat} (h : c ≤ b) (a : Nat) :
    a <<< b >>> c = a <<< (b - c) := by
  obtain ⟨b, rfl⟩ := h.dest
  simp [shiftLeft_eq, Nat.pow_add, shiftRight_eq_div_pow, Nat.mul_left_comm a]
lemma testBit_toDoubleBitVector_shiftRight_sub {q a b c i k : ℕ} (hkq : k ≤ q) :
    Nat.testBit (toDoubleBitVector q a b c >>> (q - k)) i = true ↔
      i = k ∨ i = k + a ∨ i = k + b ∨ i = k + c ∨
        i + q = k ∨ i + q = k + a ∨ i + q = k + b ∨ i + q = k + c := by
  rw [toDoubleBitVector, Nat.shiftRight_or_distrib,
    Nat.shiftLeft_shiftRight_eq_shiftLeft_of_le (by grind), Nat.sub_sub_self hkq]
  simp [testBit_toBitVector]
  grind
lemma testBit_toDoubleBitVector_shiftRight {q a b c i k : ℕ} (hkq : k ≤ q) :
    Nat.testBit (toDoubleBitVector q a b c >>> (q - k)) i = true →
      (i - k : ZMod q) ∈ ({0, (a : ZMod q), (b : ZMod q), (c : ZMod q)} : Finset (ZMod q)) := by
  rw [testBit_toDoubleBitVector_shiftRight_sub (k := k) hkq]
  simp only [mem_insert, mem_singleton]
  rintro (h₁ | h₁ | h₁ | h₁ | h₁ | h₁ | h₁ | h₁)
  all_goals
    replace h₁ := congr(($h₁ : ZMod q))
    grind [Nat.cast_add, ZMod.natCast_self]
lemma testBit_shiftRight_toDoubleBitVector {q a b c k z : ℕ} (hkq : k ≤ q) (hz : z < 2 ^ q)
    (h : 0 < (toDoubleBitVector q a b c >>> (q - k)) &&& z) :
    ∃ i < q, (i - k : ZMod q) ∈ ({0, (a : ZMod q), (b : ZMod q), (c : ZMod q)} : Finset (ZMod q)) ∧
      z.testBit i = true := by
  simp only [Nat.pos_iff_ne_zero, ne_eq] at h
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h
  rw [Nat.testBit_and, Bool.and_eq_true] at hi
  refine ⟨i, ?_, testBit_toDoubleBitVector_shiftRight hkq hi.1, hi.2⟩
  by_contra!
  grw [this] at hz
  · simp [Nat.testBit_lt_two_pow hz] at hi
  · simp
noncomputable def checkValid (q v x y z : ℕ) : Bool :=
  q.rec true fun i acc ↦
    let v' := v.shiftRight (q.sub i)
    ((Nat.ble (nat_lit 1) (v'.land x)).and'
      ((Nat.ble (nat_lit 1) (v'.land y)).and'
        (Nat.ble (nat_lit 1) (v'.land z)))).and' acc
lemma rec_and {q : ℕ} (P : ℕ → Bool) :
    Nat.rec true (fun i acc ↦ (P i).and' acc) q = true ↔ ∀ i < q, P i := by
  induction q with
  | zero => simp
  | succ n ih =>
    dsimp
    rw [Bool.and'_eq_and, Bool.and_eq_true, ih, Nat.forall_lt_succ_right, and_comm]
lemma helper {a q aq : ℕ} (ha : (a.mod q).beq aq) : (a : ZMod q) = aq := by
  simp_all [← ZMod.natCast_mod]
lemma ZMod.cases_of_neZero {q : ℕ} [NeZero q] {P : ZMod q → Prop}
    (h : ∀ r : ℕ, r < q → P r) :
    ∀ z : ZMod q, P z := by
  cases q with
  | zero => simp_all
  | succ q =>
    intro r
    simpa using h r.val (ZMod.val_lt _)
lemma or_lt_two_pow_iff {x y n : Nat} : x ||| y < 2 ^ n ↔ x < 2 ^ n ∧ y < 2 ^ n := by
  constructor
  · intro h
    exact ⟨Nat.lt_of_le_of_lt Nat.left_le_or h, Nat.lt_of_le_of_lt Nat.right_le_or h⟩
  · rintro ⟨hx, hy⟩
    exact Nat.or_lt_two_pow hx hy
lemma mainProof {q a b c v v' x y z : ℕ}
    (hv' : v'.beq (toBitVectorK a b c))
    (hv : v.beq (v'.lor (v'.shiftLeft q)))
    (hq : Nat.ble (nat_lit 1) q)
    (hxy : Nat.beq (x.land y) (nat_lit 0))
    (hxz : Nat.beq (x.land z) (nat_lit 0))
    (hyz : Nat.beq (y.land z) (nat_lit 0))
    (hxyz : ((x.lor y).lor z).succ.ble (Nat.shiftLeft (nat_lit 1) q))
    (hvalid : checkValid q v x y z) :
    ModAccept q a b c := by
  simp only [Nat.shiftLeft_eq', Nat.lor_eq, Nat.beq_eq, Nat.ble_eq, Nat.land_eq,
    Nat.one_shiftLeft, toBitVectorK_eq] at hv hv' hq hxy hxz hyz hxyz
  replace hv : v = toDoubleBitVector q a b c := by
    rw [hv, hv']
    simp [toDoubleBitVector]
  have : NeZero q := ⟨by grind⟩
  intro aq bq cq haq hbq hcq
  rw [Accept]
  let χ (i : ZMod q) : Fin 3 := if x.testBit i.val then 0 else if y.testBit i.val then 1 else 2
  have hχx (i : ZMod q) (hi : x.testBit i.val) : χ i = 0 := by simp [χ, hi]
  have hχy (i : ZMod q) (hi : y.testBit i.val) : χ i = 1 := by
    simp only [Fin.isValue, hi, ↓reduceIte, ite_eq_right_iff, zero_ne_one, imp_false,
      Bool.not_eq_true, χ]
    by_contra!
    have : (x &&& y).testBit i.val = true := by grind
    simp [hxy] at this
  have hχz (i : ZMod q) (hi : z.testBit i.val) : χ i = 2 := by
    have : x.testBit i.val ≠ true := by
      intro h
      have : (x &&& z).testBit i.val = true := by grind
      simp [hxz] at this
    have : y.testBit i.val ≠ true := by
      intro h
      have : (y &&& z).testBit i.val = true := by grind
      simp [hyz] at this
    simp_all [χ]
  apply HasPolychromColouring.of_image (Int.castAddHom (ZMod q))
  refine ⟨χ, ?_⟩
  simp only [Int.coe_castAddHom, image_insert, Int.cast_zero, Int.cast_natCast, helper haq,
    helper hbq, image_singleton, helper hcq]
  rw [checkValid, rec_and] at hvalid
  apply ZMod.cases_of_neZero
  intro i hi
  specialize hvalid i hi
  simp only [Bool.and'_eq_and, Nat.sub_eq, Nat.shiftRight_eq, Bool.and_eq_true,
    Nat.ble_eq, hv, Nat.land_eq] at hvalid
  simp only [Fin.forall_fin_succ, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    IsEmpty.forall_iff, and_true]
  simp only [Nat.succ_le_iff, or_lt_two_pow_iff] at hxyz
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨j, hjq, hj, hjx⟩ :=
      testBit_shiftRight_toDoubleBitVector (by grind) (by grind) hvalid.1
    refine ⟨j - (i : ℕ), hj, ?_⟩
    simp only [add_sub_cancel, Fin.isValue]
    apply hχx j
    simpa [Nat.mod_eq_of_lt hjq]
  · obtain ⟨j, hjq, hj, hjy⟩ :=
      testBit_shiftRight_toDoubleBitVector (by grind) (by grind) hvalid.2.1
    refine ⟨j - (i : ℕ), hj, ?_⟩
    simp only [add_sub_cancel, Fin.isValue]
    apply hχy j
    simpa [Nat.mod_eq_of_lt hjq]
  · obtain ⟨j, hjq, hj, hjz⟩ :=
      testBit_shiftRight_toDoubleBitVector (by grind) (by grind) hvalid.2.2
    refine ⟨j - (i : ℕ), hj, ?_⟩
    simp only [add_sub_cancel, Fin.isValue]
    apply hχz j
    simpa [Nat.mod_eq_of_lt hjq]
example : ModAccept 6 1 3 4 :=
  mainProof (v' := 0b011011) (v := 0b011011011011) (x := 0b000101) (y := 0b1010) (z := 0b110000)
    rfl rfl rfl rfl rfl rfl rfl rfl


