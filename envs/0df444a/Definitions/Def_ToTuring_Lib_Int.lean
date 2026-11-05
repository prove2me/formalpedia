-- Prove2me | Definitions.Def_ToTuring_Lib_Int
-- name    : ToTuring_Lib_Int
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:44:42.060857+00:00
-- url     : https://prove2.me/theorems/06230654-51c8-4acc-be43-a006b412cf60
-- title:
--   Int
-- statement:
--   Definitions and structural lemmas for Int, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Int.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Nat2
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_div_pow
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_idxOf
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_mod
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_of_wd
import Theorems.Thm_Groundwork_PolyT_optionElim
import Theorems.Thm_Groundwork_PolyT_pow_const
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_PolyT_sumElim
import Theorems.Thm_Groundwork_PolyT_testBit
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
import Theorems.Thm_Groundwork_wd_int
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
import Theorems.Thm_P2M_Groundwork_PolyT_cons__3a60f43a3b86
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_P2M_Groundwork_PolyT_inl__78f4b62d65a1
import Theorems.Thm_P2M_Groundwork_PolyT_inr__53ca1f30b2d3
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
import Theorems.Thm_P2M_Groundwork_PolyT_log2__935ea318e2e8
import Theorems.Thm_P2M_Groundwork_PolyT_size__c8c8eb1b342f
import Theorems.Thm_P2M_Groundwork_PolyT_some__e6a32bd6af45
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.countP
attribute [local fun_prop] Groundwork.PolyT.div
attribute [local fun_prop] Groundwork.PolyT.div_pow
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.idxOf
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.mod
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.optionElim
attribute [local fun_prop] Groundwork.PolyT.pow_const
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sum
attribute [local fun_prop] Groundwork.PolyT.sumElim
attribute [local fun_prop] Groundwork.PolyT.testBit
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_inl__78f4b62d65a1
attribute [local fun_prop] P2M_Groundwork_PolyT_inr__53ca1f30b2d3
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] P2M_Groundwork_PolyT_log2__935ea318e2e8
attribute [local fun_prop] P2M_Groundwork_PolyT_size__c8c8eb1b342f
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
def sgn (z : ℤ) : Bool := decide (z < 0)
def mkZ (s : Bool) (n : ℕ) : ℤ := bif s then -(n : ℤ) else (n : ℤ)
theorem sgn_mkZ (s : Bool) (n : ℕ) : sgn (mkZ s n) = (s && decide (n ≠ 0)) := by
  cases s
  · have h : ¬ (mkZ false n < 0) := by
      simp only [mkZ, cond_false]
      omega
    simp only [sgn, h, decide_false, Bool.false_and]
  · by_cases h : n = 0
    · subst h
      have h' : ¬ (mkZ true 0 < 0) := by
        simp only [mkZ, cond_true]
        omega
      simp only [sgn, h', decide_false, Bool.true_and, ne_eq, not_true_eq_false]
    · have h' : mkZ true n < 0 := by
        simp only [mkZ, cond_true]
        omega
      simp only [sgn, h', decide_true, Bool.true_and, ne_eq, h, not_false_eq_true]
theorem natAbs_mkZ (s : Bool) (n : ℕ) : (mkZ s n).natAbs = n := by
  cases s <;> simp [mkZ]
theorem rep {f : α → ℤ} (hf : PolyT f) : PolyT (fun x => (sgn (f x), (f x).natAbs)) :=
  of_wd hf id (fun _ => rfl) fun _ => rfl
@[fun_prop] theorem sgn' {f : α → ℤ} (hf : PolyT f) : PolyT (fun x => sgn (f x)) :=
  (rep hf).fst
@[fun_prop] theorem natAbs {f : α → ℤ} (hf : PolyT f) :
    PolyT (fun x => (f x).natAbs) :=
  (rep hf).snd
@[fun_prop] theorem mkZ' {s : α → Bool} {n : α → ℕ} (hs : PolyT s) (hn : PolyT n) :
    PolyT (fun x => mkZ (s x) (n x)) := by
  have h : PolyT (fun x => (s x && decide (n x ≠ 0), n x)) := by fun_prop
  refine of_wd h id (fun _ => rfl) fun x => ?_
  rw [wd_int]
  change wd (sgn (mkZ (s x) (n x)), (mkZ (s x) (n x)).natAbs) = _
  rw [sgn_mkZ, natAbs_mkZ]
  rfl
@[fun_prop] theorem natCast {f : α → ℕ} (hf : PolyT f) :
    PolyT (fun x => (f x : ℤ)) :=
  (mkZ' (const false) hf).congr fun _ => rfl
@[fun_prop] theorem toNat {f : α → ℤ} (hf : PolyT f) :
    PolyT (fun x => (f x).toNat) := by
  have h : PolyT (fun x => bif sgn (f x) then 0 else (f x).natAbs) := by fun_prop
  refine h.congr fun x => ?_
  by_cases h0 : f x < 0 <;> simp only [sgn, h0, decide_true, decide_false, cond_true, cond_false] <;> omega
@[fun_prop] theorem negZ {f : α → ℤ} (hf : PolyT f) :
    PolyT (fun x => - f x) := by
  have h : PolyT (fun x => mkZ (!sgn (f x)) (f x).natAbs) := by fun_prop
  refine h.congr fun x => ?_
  by_cases h0 : f x < 0 <;> simp only [sgn, mkZ, h0, decide_true, decide_false, Bool.not_true, Bool.not_false, cond_true, cond_false] <;> omega
theorem add_eq (z w : ℤ) :
    (bif sgn z ^^ sgn w then
      (bif decide (w.natAbs ≤ z.natAbs) then mkZ (sgn z) (z.natAbs - w.natAbs) else mkZ (sgn w) (w.natAbs - z.natAbs))
    else mkZ (sgn z) (z.natAbs + w.natAbs)) = z + w := by
  by_cases h0 : z < 0 <;> by_cases h1 : w < 0 <;> by_cases h2 : w.natAbs ≤ z.natAbs <;> simp only [sgn, mkZ, h0, h1, h2, decide_true, decide_false, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false,
      cond_true, cond_false] <;> omega
@[fun_prop] theorem addZ {f g : α → ℤ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x + g x) := by
  have h : PolyT (fun x => bif sgn (f x) ^^ sgn (g x) then
      (bif decide ((g x).natAbs ≤ (f x).natAbs) then mkZ (sgn (f x)) ((f x).natAbs - (g x).natAbs)
        else mkZ (sgn (g x)) ((g x).natAbs - (f x).natAbs))
      else mkZ (sgn (f x)) ((f x).natAbs + (g x).natAbs)) := by fun_prop
  exact h.congr fun x => add_eq _ _
@[fun_prop] theorem subZ {f g : α → ℤ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x - g x) :=
  (addZ hf (negZ hg)).congr fun x => (sub_eq_add_neg (f x) (g x)).symm
theorem mul_eq (z w : ℤ) : mkZ (sgn z ^^ sgn w) (z.natAbs * w.natAbs) = z * w := by
  by_cases h0 : z < 0 <;> by_cases h1 : w < 0 <;> simp only [sgn, mkZ, h0, h1, decide_true, decide_false, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false,
      cond_true, cond_false, Nat.cast_mul]
  · rw [show (z.natAbs : ℤ) = -z by omega, show (w.natAbs : ℤ) = -w by omega]
    ring
  · rw [show (z.natAbs : ℤ) = -z by omega, show (w.natAbs : ℤ) = w by omega]
    ring
  · rw [show (z.natAbs : ℤ) = z by omega, show (w.natAbs : ℤ) = -w by omega]
    ring
  · rw [show (z.natAbs : ℤ) = z by omega, show (w.natAbs : ℤ) = w by omega]
@[fun_prop] theorem mulZ {f g : α → ℤ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x * g x) := by
  have h : PolyT (fun x => mkZ (sgn (f x) ^^ sgn (g x)) ((f x).natAbs * (g x).natAbs)) := by fun_prop
  exact h.congr fun x => mul_eq _ _
@[fun_prop] theorem decide_ltZ {f g : α → ℤ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => decide (f x < g x)) :=
  (sgn' (subZ hf hg)).congr fun x => by
    simp only [sgn, decide_eq_decide]
    omega
@[fun_prop] theorem decide_leZ {f g : α → ℤ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => decide (f x ≤ g x)) :=
  (not' (sgn' (subZ hg hf))).congr fun x => by
    by_cases h : f x ≤ g x
    · have h' : ¬ (g x - f x < 0) := by omega
      simp [sgn, h, h']
    · have h' : g x - f x < 0 := by omega
      simp [sgn, h, h']
instance : EqT ℤ := ⟨by
  have h : PolyT (fun p : ℤ × ℤ => decide ((sgn p.1, p.1.natAbs) = (sgn p.2, p.2.natAbs))) := by fun_prop
  refine h.congr fun p => ?_
  simp only [sgn, Prod.mk.injEq, decide_eq_decide]
  omega⟩
end Groundwork.PolyT


