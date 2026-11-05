-- Prove2me | Definitions.Def_ToTuring_Lib_List2
-- name    : ToTuring_Lib_List2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:23:26.456431+00:00
-- url     : https://prove2.me/theorems/b1a54ee0-2a65-4cb9-9692-413d2bab8898
-- title:
--   List2
-- statement:
--   Definitions and structural lemmas for List2, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List2.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_StepMachines_Prog_Chunks
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_foldl_add
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_idxOf
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_optionElim
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_PolyT_sumElim
import Theorems.Thm_Groundwork_PolyT_testBit
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
import Theorems.Thm_Groundwork_len_append
import Theorems.Thm_Groundwork_len_drop_le
import Theorems.Thm_Groundwork_len_nat_mono
import Theorems.Thm_Groundwork_length_le_len
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
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
import Theorems.Thm_P2M_Groundwork_PolyT_log2__935ea318e2e8
import Theorems.Thm_P2M_Groundwork_PolyT_size__c8c8eb1b342f
import Theorems.Thm_P2M_Groundwork_PolyT_some__e6a32bd6af45
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.countP
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.idxOf
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.optionElim
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
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
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
theorem foldl_drop {ε β : Type} (m : List ε) (n : ℕ) (l : List β) :
    m.foldl (fun (s : ℕ × List β) (_ : ε) => (s.1 - 1, if s.1 = 0 then s.2 else s.2.tail)) (n, l)
      = (n - m.length, l.drop (min n m.length)) := by
  induction m generalizing n l with
  | nil => simp
  | cons e m ih =>
    rw [List.foldl_cons, ih]
    cases n with
    | zero => simp
    | succ n => simp
theorem drop_min_length {β : Type} (n : ℕ) (l : List β) : l.drop (min n l.length) = l.drop n := by
  rcases Nat.le_total n l.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.drop_length, List.drop_eq_nil_of_le h]
@[fun_prop] theorem drop {n : α → ℕ} {l : α → List β} (hn : PolyT n) (hl : PolyT l) :
    PolyT (fun x => (l x).drop (n x)) := by
  have h : PolyT fun x => (l x).foldl
      (fun (s : ℕ × List β) (_ : β) => (s.1 - 1, if s.1 = 0 then s.2 else s.2.tail)) (n x, l x) := by
    refine foldl_add (g := fun _ (s : ℕ × List β) (_ : β) => (s.1 - 1, if s.1 = 0 then s.2 else s.2.tail))
      hl (by fun_prop) (by fun_prop) ⟨fun _ => 0, PB.const 0, ?_⟩
    rintro x ⟨k, r⟩ e -
    have h1 : len (k - 1) ≤ len k := len_nat_mono (Nat.sub_le k 1)
    have h2 : len (if k = 0 then r else r.tail) ≤ len r := by
      split_ifs
      · exact le_rfl
      · rw [← List.drop_one]; exact len_drop_le r 1
    simp only [len_pair]
    omega
  exact h.snd.congr fun x => by rw [foldl_drop, drop_min_length]
@[fun_prop] theorem take {n : α → ℕ} {l : α → List β} (hn : PolyT n) (hl : PolyT l) :
    PolyT (fun x => (l x).take (n x)) := by
  have h : PolyT fun x => ((l x).reverse.drop ((l x).length - n x)).reverse := by fun_prop
  exact h.congr fun x => by
    have := List.take_reverse (xs := (l x).reverse) (i := n x)
    simpa using this.symm
@[fun_prop] theorem getElem? {n : α → ℕ} {l : α → List β} (hl : PolyT l) (hn : PolyT n) :
    PolyT (fun x => (l x)[n x]?) := by
  have h : PolyT fun x => ((l x).drop (n x)).head? := by fun_prop
  exact h.congr fun x => List.head?_drop
@[fun_prop] theorem getD {n : α → ℕ} {l : α → List β} {d : α → β} (hl : PolyT l) (hn : PolyT n) (hd : PolyT d) :
    PolyT (fun x => (l x).getD (n x) (d x)) := by
  have h : PolyT fun x => ((l x)[n x]?).getD (d x) := by fun_prop
  exact h.congr fun x => List.getD_eq_getElem?_getD.symm
theorem foldl_range {ε : Type} (m : List ε) (j : ℕ) :
    m.foldl (fun (a : List ℕ) (_ : ε) => a ++ [a.length]) (List.range j) = List.range (j + m.length) := by
  induction m generalizing j with
  | nil => simp
  | cons e m ih =>
    rw [List.foldl_cons, List.length_range, ← List.range_succ, ih, List.length_cons]
    congr 1; omega
theorem len_range_le {m M : ℕ} (h : m ≤ M) : len (List.range m) ≤ m * (3 * M + 4) + 2 := by
  induction m with
  | zero => simp [len_nil]
  | succ m ih =>
    have h1 := ih (by omega)
    have h2 := len_append (List.range m) [m]
    have h3 : len [m] = len m + 4 := by rw [len_cons, len_nil]
    have h4 : Nat.size m ≤ m := Nat.size_le.2 Nat.lt_two_pow_self
    rw [List.range_succ, Nat.succ_mul]
    rw [h3, len_nat] at h2
    omega
theorem range {n : α → ℕ} (hn : Unary n) :
    PolyT (fun x => List.range (n x)) := by
  have hn' : PolyT fun x => List.replicate (n x) () := hn
  obtain ⟨-, t, ht, -, -, hlen⟩ := hn'.elim
  have h : PolyT fun x => (List.replicate (n x) ()).foldl
      (fun (a : List ℕ) (_ : Unit) => a ++ [a.length]) (List.range 0) := by
    refine foldl (g := fun _ (a : List ℕ) (_ : Unit) => a ++ [a.length]) hn' (by fun_prop) (by fun_prop)
      ⟨fun N => t N * (3 * t N + 4) + 2, (ht.mul (((PB.const 3).mul ht).add (PB.const 4))).add (PB.const 2), ?_⟩
    intro x k
    rw [foldl_range]
    have h1 : 0 + ((List.replicate (n x) ()).take k).length ≤ t (len x) := by
      have := length_le_len (List.replicate (n x) ())
      have := hlen x
      have := List.length_take_le' k (List.replicate (n x) ())
      omega
    exact (len_range_le h1).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ h1) 2)
  exact h.congr fun x => by rw [foldl_range]; simp
end Groundwork.PolyT


