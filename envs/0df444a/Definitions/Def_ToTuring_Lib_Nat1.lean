-- Prove2me | Definitions.Def_ToTuring_Lib_Nat1
-- name    : ToTuring_Lib_Nat1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T18:32:42.678833+00:00
-- url     : https://prove2.me/theorems/5d5ce532-78bf-4455-93e1-78bc30b6e96d
-- title:
--   Nat1
-- statement:
--   Definitions and structural lemmas for Nat1, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat1.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_List1b
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_foldl_add
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_optionElim
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sumElim
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
import Theorems.Thm_P2M_Groundwork_PolyT_cons__3a60f43a3b86
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_P2M_Groundwork_PolyT_inl__78f4b62d65a1
import Theorems.Thm_P2M_Groundwork_PolyT_inr__53ca1f30b2d3
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
import Theorems.Thm_P2M_Groundwork_PolyT_some__e6a32bd6af45
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.optionElim
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sumElim
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_inl__78f4b62d65a1
attribute [local fun_prop] P2M_Groundwork_PolyT_inr__53ca1f30b2d3
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] P2M_Groundwork_PolyT_some__e6a32bd6af45
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit


set_option autoImplicit false
section
section
namespace Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
def bval (w : List Bool) : ℕ := w.foldr Nat.bit 0
theorem bval_nil : bval [] = 0 := rfl
theorem bval_cons (b : Bool) (w : List Bool) : bval (b :: w) = 2 * bval w + b.toNat := by
  simp [bval, Nat.bit_val]
theorem bval_eq (w : List Bool) : bval w = 2 * bval w.tail + (w.headD false).toNat := by
  cases w <;> simp [bval_cons, bval_nil]
theorem bval_bits (n : ℕ) : bval (Nat.bits n) = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bval_nil]
  | bit b n h ih => rw [Nat.bits_append_bit _ _ h, bval_cons, ih, Nat.bit_val]
theorem bval_lt (w : List Bool) : bval w < 2 ^ w.length := by
  induction w with
  | nil => simp [bval_nil]
  | cons b w ih =>
    rw [bval_cons, List.length_cons, pow_succ]
    cases b <;> simp <;> omega
theorem eq_zero_of_bits_eq_nil {n : ℕ} (h : Nat.bits n = []) : n = 0 := by
  rw [← bval_bits n, h, bval_nil]
def bitsTrim (w : List Bool) : List Bool :=
  w.foldr (fun b r => bif !b && r.isEmpty then [] else b :: r) []
theorem bitsTrim_cons (b : Bool) (w : List Bool) :
    bitsTrim (b :: w) = bif !b && (bitsTrim w).isEmpty then [] else b :: bitsTrim w := rfl
theorem bits_bval (w : List Bool) : Nat.bits (bval w) = bitsTrim w := by
  induction w with
  | nil => simp [bval_nil, bitsTrim]
  | cons b w ih =>
    rw [bitsTrim_cons, ← ih]
    by_cases h0 : bval w = 0
    · cases b
      · simp [bval_cons, h0]
      · have : bval (true :: w) = Nat.bit true (bval w) := rfl
        rw [this, Nat.bits_append_bit _ _ (fun _ => rfl)]; simp
    · have h1 : Nat.bits (bval w) ≠ [] := fun h => h0 (eq_zero_of_bits_eq_nil h)
      have : bval (b :: w) = Nat.bit b (bval w) := rfl
      have h2 : (Nat.bits (bval w)).isEmpty = false := by
        cases hh : Nat.bits (bval w) with
        | nil => exact absurd hh h1
        | cons _ _ => rfl
      rw [this, Nat.bits_append_bit _ _ (fun h => absurd h h0), h2, Bool.and_false, cond_false]
theorem length_bitsTrim_le (w : List Bool) : (bitsTrim w).length ≤ w.length := by
  induction w with
  | nil => simp [bitsTrim]
  | cons b w ih =>
    rw [bitsTrim_cons]
    cases h : (!b && (bitsTrim w).isEmpty) <;> simp
    omega
theorem of_bits {f : α → ℕ} (hf : PolyT fun x => Nat.bits (f x)) : PolyT f := hf
theorem bitsTrim' {w : α → List Bool} (hw : PolyT w) : PolyT (fun x => bitsTrim (w x)) := by
  obtain ⟨t, ht, _, hl⟩ := len_bound hw
  refine foldr (g := fun _ b r => bif !b && r.isEmpty then [] else b :: r) hw (const []) (by fun_prop)
    ⟨t, ht, fun x k => ?_⟩
  refine le_trans ?_ (hl x)
  have h := length_bitsTrim_le ((w x).drop k)
  have h' : ((w x).drop k).length ≤ (w x).length := by simp
  change len (bitsTrim ((w x).drop k)) ≤ _
  rw [len_bools, len_bools]
  omega
@[fun_prop] theorem bits {f : α → ℕ} (hf : PolyT f) :
    PolyT (fun x => Nat.bits (f x)) := hf
theorem ofBits {w : α → List Bool} (hw : PolyT w) :
    PolyT (fun x => (w x).foldr Nat.bit 0) :=
  of_bits ((bitsTrim' hw).congr fun x => (bits_bval (w x)).symm)
@[fun_prop] theorem bval' {w : α → List Bool} (hw : PolyT w) : PolyT (fun x => bval (w x)) := ofBits hw
def bitStep (φ : Bool × Bool × Bool → Bool × Bool) (s : Bool × List Bool × List Bool × List Bool) :
    Bool × List Bool × List Bool × List Bool :=
  ((φ (s.1, s.2.1.headD false, s.2.2.1.headD false)).1, s.2.1.tail, s.2.2.1.tail,
    (φ (s.1, s.2.1.headD false, s.2.2.1.headD false)).2 :: s.2.2.2)
def bitRun (φ : Bool × Bool × Bool → Bool × Bool) : List Bool → Bool → List Bool → List Bool → Bool × List Bool
  | [], c, _, _ => (c, [])
  | _ :: L, c, u, v =>
    ((bitRun φ L (φ (c, u.headD false, v.headD false)).1 u.tail v.tail).1,
      (φ (c, u.headD false, v.headD false)).2 :: (bitRun φ L (φ (c, u.headD false, v.headD false)).1 u.tail v.tail).2)
theorem length_bitRun (φ : Bool × Bool × Bool → Bool × Bool) (L : List Bool) (c : Bool) (u v : List Bool) :
    (bitRun φ L c u v).2.length = L.length := by
  induction L generalizing c u v with
  | nil => rfl
  | cons e L ih => simp [bitRun, ih]
theorem foldl_bitStep (φ : Bool × Bool × Bool → Bool × Bool) (L : List Bool) (c : Bool) (u v out : List Bool) :
    (L.foldl (fun s _ => bitStep φ s) (c, u, v, out)).1 = (bitRun φ L c u v).1 ∧
      (L.foldl (fun s _ => bitStep φ s) (c, u, v, out)).2.2.2 = (bitRun φ L c u v).2.reverse ++ out := by
  induction L generalizing c u v out with
  | nil => simp [bitRun]
  | cons e L ih =>
    obtain ⟨h1, h2⟩ := ih (φ (c, u.headD false, v.headD false)).1 u.tail v.tail
      ((φ (c, u.headD false, v.headD false)).2 :: out)
    refine ⟨h1, ?_⟩
    refine h2.trans ?_
    simp [bitRun]
theorem bitRun' {φ : Bool × Bool × Bool → Bool × Bool} (hφ : PolyT φ) {L u v : α → List Bool} {c : α → Bool}
    (hL : PolyT L) (hc : PolyT c) (hu : PolyT u) (hv : PolyT v) :
    PolyT (fun x => bitRun φ (L x) (c x) (u x) (v x)) := by
  have h : PolyT (fun x => (L x).foldl (fun s _ => bitStep φ s) (c x, u x, v x, [])) := by
    refine foldl_add (g := fun _ s _ => bitStep φ s) hL (by fun_prop) (by unfold bitStep; fun_prop)
      ⟨fun _ => 3, PB.const 3, fun x s e _ => ?_⟩
    have hb : ∀ b : Bool, len b = 1 := fun _ => rfl
    obtain ⟨c, u, v, out⟩ := s
    simp only [bitStep, len_pair, len_bools, hb, List.length_tail, List.length_cons]
    omega
  have h2 : PolyT (fun x => (((L x).foldl (fun s _ => bitStep φ s) (c x, u x, v x, [])).1,
      ((L x).foldl (fun s _ => bitStep φ s) (c x, u x, v x, [])).2.2.2.reverse)) := by fun_prop
  refine h2.congr fun x => ?_
  obtain ⟨h1, h2⟩ := foldl_bitStep φ (L x) (c x) (u x) (v x) []
  rw [h1, h2]; simp
def addφ (p : Bool × Bool × Bool) : Bool × Bool :=
  ((p.1 && p.2.1) || (p.1 && p.2.2) || (p.2.1 && p.2.2), p.1 ^^ p.2.1 ^^ p.2.2)
theorem addφ_spec (c x y : Bool) :
    2 * (addφ (c, x, y)).1.toNat + (addφ (c, x, y)).2.toNat = c.toNat + x.toNat + y.toNat := by
  cases c <;> cases x <;> cases y <;> rfl
theorem bval_bitRun_add (L : List Bool) (c : Bool) (u v : List Bool) (h : bval u + bval v + c.toNat < 2 ^ L.length) :
    bval (bitRun addφ L c u v).2 = bval u + bval v + c.toNat := by
  induction L generalizing c u v with
  | nil =>
    simp only [List.length_nil, pow_zero] at h
    simp only [bitRun, bval_nil]; omega
  | cons e L ih =>
    have hu := bval_eq u
    have hv := bval_eq v
    have hs := addφ_spec c (u.headD false) (v.headD false)
    rw [List.length_cons, pow_succ] at h
    have := ih (addφ (c, u.headD false, v.headD false)).1 u.tail v.tail (by omega)
    simp only [bitRun, bval_cons]
    omega
theorem bval_addRun (a b : ℕ) :
    bval (bitRun addφ (false :: (Nat.bits a ++ Nat.bits b)) false (Nat.bits a) (Nat.bits b)).2 = a + b := by
  have ha := bval_lt (Nat.bits a)
  have hb := bval_lt (Nat.bits b)
  rw [bval_bitRun_add]
  · simp [bval_bits]
  · rw [List.length_cons, List.length_append, pow_succ, pow_add]
    have h1 : 1 ≤ 2 ^ (Nat.bits a).length := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ (Nat.bits b).length := Nat.one_le_two_pow
    simp only [Bool.toNat_false, add_zero]
    nlinarith
theorem add_aux {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) : PolyT (fun x => f x + g x) := by
  have hφ : PolyT addφ := by unfold addφ; fun_prop
  have h := bitRun' hφ (L := fun x => false :: (Nat.bits (f x) ++ Nat.bits (g x))) (c := fun _ => false)
    (u := fun x => Nat.bits (f x)) (v := fun x => Nat.bits (g x)) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  exact (bval' (snd h)).congr fun x => bval_addRun (f x) (g x)
def subφ (p : Bool × Bool × Bool) : Bool × Bool :=
  ((!p.2.1 && (p.2.2 || p.1)) || (p.2.2 && p.1), p.1 ^^ p.2.1 ^^ p.2.2)
theorem subφ_spec (c x y : Bool) :
    (subφ (c, x, y)).2.toNat + y.toNat + c.toNat = x.toNat + 2 * (subφ (c, x, y)).1.toNat := by
  cases c <;> cases x <;> cases y <;> rfl
theorem bval_bitRun_sub (L : List Bool) (c : Bool) (u v : List Bool) (hu : bval u < 2 ^ L.length)
    (hv : bval v < 2 ^ L.length) :
    bval (bitRun subφ L c u v).2 + bval v + c.toNat = bval u + 2 ^ L.length * (bitRun subφ L c u v).1.toNat := by
  induction L generalizing c u v with
  | nil =>
    simp only [List.length_nil, pow_zero] at hu hv ⊢
    simp only [bitRun, bval_nil]; omega
  | cons e L ih =>
    have hu' := bval_eq u
    have hv' := bval_eq v
    have hs := subφ_spec c (u.headD false) (v.headD false)
    rw [List.length_cons, pow_succ] at hu hv
    have := ih (subφ (c, u.headD false, v.headD false)).1 u.tail v.tail (by omega) (by omega)
    simp only [bitRun, bval_cons, List.length_cons, pow_succ]
    rw [mul_right_comm]
    omega
def subRun (a b : ℕ) : Bool × List Bool :=
  bitRun subφ (Nat.bits a ++ Nat.bits b) false (Nat.bits a) (Nat.bits b)
theorem subRun_spec (a b : ℕ) :
    (subRun a b).1 = decide (a < b) ∧ ((subRun a b).1 = false → bval (subRun a b).2 = a - b) := by
  have hle : ∀ p q : ℕ, 2 ^ p ≤ 2 ^ (p + q) := fun p q => Nat.pow_le_pow_right (by norm_num) (by omega)
  have ha : bval (Nat.bits a) < 2 ^ (Nat.bits a ++ Nat.bits b).length := by
    rw [List.length_append]; exact lt_of_lt_of_le (bval_lt _) (hle _ _)
  have hb : bval (Nat.bits b) < 2 ^ (Nat.bits a ++ Nat.bits b).length := by
    rw [List.length_append, add_comm]; exact lt_of_lt_of_le (bval_lt _) (hle _ _)
  have h := bval_bitRun_sub _ false _ _ ha hb
  have hl := bval_lt (subRun a b).2
  rw [subRun, length_bitRun] at hl
  rw [bval_bits] at h ha hb
  rw [bval_bits] at h
  change bval (subRun a b).2 + b + _ = a + _ * (subRun a b).1.toNat at h
  change bval (subRun a b).2 < _ at hl
  cases hc : (subRun a b).1
  · rw [hc] at h
    simp only [Bool.toNat_false, add_zero, mul_zero] at h
    refine ⟨?_, fun _ => by omega⟩
    symm; rw [decide_eq_false_iff_not]; omega
  · rw [hc] at h
    simp only [Bool.toNat_false, Bool.toNat_true, add_zero, mul_one] at h
    refine ⟨?_, fun h => by cases h⟩
    symm; rw [decide_eq_true_iff]; omega
theorem subRun' {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) : PolyT (fun x => subRun (f x) (g x)) := by
  have hφ : PolyT subφ := by unfold subφ; fun_prop
  exact bitRun' hφ (L := fun x => Nat.bits (f x) ++ Nat.bits (g x)) (c := fun _ => false)
    (u := fun x => Nat.bits (f x)) (v := fun x => Nat.bits (g x)) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
theorem sub_aux {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) : PolyT (fun x => f x - g x) := by
  have h := subRun' hf hg
  have h2 : PolyT (fun x => bif (subRun (f x) (g x)).1 then 0 else bval (subRun (f x) (g x)).2) := by fun_prop
  refine h2.congr fun x => ?_
  obtain ⟨h1, h3⟩ := subRun_spec (f x) (g x)
  cases hc : (subRun (f x) (g x)).1
  · simpa using h3 hc
  · rw [hc] at h1
    have : f x < g x := by simpa using h1.symm
    simp only [cond_true]; omega
@[fun_prop] theorem add {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x + g x) := add_aux hf hg
@[fun_prop] theorem sub {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x - g x) := sub_aux hf hg
@[fun_prop] theorem decide_le {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => decide (f x ≤ g x)) := by
  refine (not' (fst (subRun' hg hf))).congr fun x => ?_
  rw [(subRun_spec (g x) (f x)).1]
  by_cases h : f x ≤ g x
  · simp [h, Nat.not_lt.mpr h]
  · simp [h, Nat.lt_of_not_le h]
@[fun_prop] theorem decide_lt {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => decide (f x < g x)) :=
  (fst (subRun' hf hg)).congr fun x => (subRun_spec (f x) (g x)).1
@[fun_prop] theorem min' {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => min (f x) (g x)) := by
  have h : PolyT (fun x => if f x ≤ g x then f x else g x) := by fun_prop
  exact h.congr fun x => (Nat.min_def ..).symm
@[fun_prop] theorem max' {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => max (f x) (g x)) := by
  have h : PolyT (fun x => if f x ≤ g x then g x else f x) := by fun_prop
  exact h.congr fun x => (Nat.max_def ..).symm
instance : EqT ℕ := ⟨by
  have h : PolyT (fun p : ℕ × ℕ => decide (Nat.bits p.1 = Nat.bits p.2)) := by fun_prop
  refine h.congr fun p => ?_
  refine decide_eq_decide.mpr ⟨fun e => ?_, fun e => by rw [e]⟩
  rw [← bval_bits p.1, e, bval_bits]⟩
end Groundwork.PolyT


