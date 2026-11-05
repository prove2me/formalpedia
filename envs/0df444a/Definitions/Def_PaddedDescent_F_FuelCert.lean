-- Prove2me | Definitions.Def_PaddedDescent_F_FuelCert
-- name    : PaddedDescent_F_FuelCert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:06:44.48558+00:00
-- url     : https://prove2.me/theorems/c59459ed-b68d-45ad-b71e-40bd7ef8801e
-- title:
--   Fuel Cert
-- statement:
--   Definitions and structural lemmas for Fuel Cert, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/FuelCert.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ToTuring_Poly_NetFun
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_contains
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_Groundwork_PolyT_decide_mem
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_div_pow
import Theorems.Thm_Groundwork_PolyT_dropWhile
import Theorems.Thm_Groundwork_PolyT_elem
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_foldl_add
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_idxOf
import Theorems.Thm_Groundwork_PolyT_len_bound_mem
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_mod
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_optionElim
import Theorems.Thm_Groundwork_PolyT_pow_const
import Theorems.Thm_Groundwork_PolyT_pow_unary
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_product
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sprod
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_PolyT_sumElim
import Theorems.Thm_Groundwork_PolyT_takeWhile
import Theorems.Thm_Groundwork_PolyT_testBit
import Theorems.Thm_Groundwork_PolyT_unary_min_length
import Theorems.Thm_Groundwork_Prog_NetE_Pc_polyT
import Theorems.Thm_Groundwork_Prog_NetE_betaC_polyT
import Theorems.Thm_Groundwork_Prog_NetE_capWord_polyT
import Theorems.Thm_Groundwork_Prog_NetE_cap_polyT
import Theorems.Thm_Groundwork_Prog_NetE_col_polyT
import Theorems.Thm_Groundwork_Prog_NetE_lAt_polyT
import Theorems.Thm_Groundwork_Prog_NetE_labOf_polyT
import Theorems.Thm_Groundwork_Prog_NetE_lbLen_polyT
import Theorems.Thm_Groundwork_Prog_NetE_lbLens_polyT
import Theorems.Thm_Groundwork_Prog_NetE_members_polyT
import Theorems.Thm_Groundwork_Prog_NetE_n_polyT
import Theorems.Thm_Groundwork_Prog_NetE_prs_polyT
import Theorems.Thm_Groundwork_Prog_NetE_stLens_polyT
import Theorems.Thm_Groundwork_Prog_NetE_unary_sum_map
import Theorems.Thm_Groundwork_Prog_NetE_zA_polyT
import Theorems.Thm_Groundwork_Prog_NetE_zAt_polyT
import Theorems.Thm_Groundwork_Prog_NetE_zOf_polyT
import Theorems.Thm_Groundwork_Stepped_foldl_add
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
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_Groundwork_len_le_of_mem
import Theorems.Thm_Groundwork_len_list
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
import Theorems.Thm_P2M_Groundwork_PolyT_chunks__bc5b8682856d
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
import Theorems.Thm_P2M_Groundwork_PolyT_cons__3a60f43a3b86
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_P2M_Groundwork_PolyT_inl__78f4b62d65a1
import Theorems.Thm_P2M_Groundwork_PolyT_inr__53ca1f30b2d3
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
import Theorems.Thm_P2M_Groundwork_PolyT_log2__935ea318e2e8
import Theorems.Thm_P2M_Groundwork_PolyT_ofWord__0eb069943014
import Theorems.Thm_P2M_Groundwork_PolyT_size__c8c8eb1b342f
import Theorems.Thm_P2M_Groundwork_PolyT_some__e6a32bd6af45
import Theorems.Thm_P2M_Groundwork_PolyT_toWord__1c2f60d1d666
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.contains
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.countP
attribute [local fun_prop] Groundwork.PolyT.decide_mem
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.div
attribute [local fun_prop] Groundwork.PolyT.div_pow
attribute [local fun_prop] Groundwork.PolyT.dropWhile
attribute [local fun_prop] Groundwork.PolyT.elem
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
attribute [local fun_prop] Groundwork.PolyT.product
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sprod
attribute [local fun_prop] Groundwork.PolyT.sum
attribute [local fun_prop] Groundwork.PolyT.sumElim
attribute [local fun_prop] Groundwork.PolyT.takeWhile
attribute [local fun_prop] Groundwork.PolyT.testBit
attribute [local fun_prop] Groundwork.Prog.NetE.Pc_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.betaC_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.capWord_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.cap_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.col_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.lAt_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.labOf_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.lbLen_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.lbLens_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.members_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.n_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.prs_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.stLens_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.zA_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.zAt_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.zOf_polyT
attribute [local fun_prop] P2M_Groundwork_PolyT_chunks__bc5b8682856d
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_inl__78f4b62d65a1
attribute [local fun_prop] P2M_Groundwork_PolyT_inr__53ca1f30b2d3
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] P2M_Groundwork_PolyT_log2__935ea318e2e8
attribute [local fun_prop] P2M_Groundwork_PolyT_ofWord__0eb069943014
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
namespace PaddedDescent.F
open Groundwork
variable {α β γ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc ε]
attribute [fun_prop] Unary
@[fun_prop] theorem unary_comp {f : β → ℕ} {h : α → β} (hf : Unary f) (hh : PolyT h) : Unary fun x => f (h x) := hf.comp hh
@[fun_prop] theorem unary_const (n : ℕ) : Unary fun _ : α => n := Unary.const n
@[fun_prop] theorem unary_length {w : α → List γ} (hw : PolyT w) : Unary fun c => (w c).length := Unary.of_length hw
@[fun_prop] theorem unary_add {f g : α → ℕ} (hf : Unary f) (hg : Unary g) : Unary fun c => f c + g c := hf.add hg
@[fun_prop] theorem unary_mul {f g : α → ℕ} (hf : Unary f) (hg : Unary g) : Unary fun c => f c * g c := hf.mul hg
@[fun_prop] theorem unary_sub {f g : α → ℕ} (hf : Unary f) (hg : PolyT g) : Unary fun c => f c - g c :=
  Unary.of_le hf (by have := hf.poly; fun_prop) fun _ => Nat.sub_le _ _
@[fun_prop] theorem unary_div {f g : α → ℕ} (hf : Unary f) (hg : PolyT g) : Unary fun c => f c / g c :=
  Unary.of_le hf (by have := hf.poly; fun_prop) fun _ => Nat.div_le_self _ _
@[fun_prop] theorem unary_pow_const {f : α → ℕ} (hf : Unary f) (k : ℕ) : Unary fun c => f c ^ k := by
  induction k with
  | zero => simpa using unary_const (α := α) 1
  | succ k ih => simpa only [pow_succ] using ih.mul hf
@[fun_prop] theorem unary_sum_map {f : α → β → ℕ} {l : α → List β} (hf : Unary fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    Unary fun a => ((l a).map (f a)).sum := Prog.NetE.unary_sum_map hf hl
@[fun_prop] theorem range_polyT {n : α → ℕ} (hn : Unary n) : PolyT fun x => List.range (n x) := PolyT.range hn
@[fun_prop] theorem pow_polyT {b e : α → ℕ} (hb : PolyT b) (he : Unary e) : PolyT fun x => b x ^ e x := PolyT.pow_unary hb he
@[fun_prop] theorem toWord_polyT {n y : α → ℕ} (hn : Unary n) (hy : PolyT y) : PolyT fun x => toWord (n x) (y x) :=
  PolyT.toWord' hn hy
@[fun_prop] theorem replicate_polyT {n : α → ℕ} (hn : Unary n) : PolyT fun x => List.replicate (n x) () := hn
@[fun_prop] theorem rng_polyT {pad : α → U} {q : α → ℕ} (hp : PolyT pad) (hq : PolyT q) : PolyT fun x => rng (pad x) (q x) :=
  PolyT.range (PolyT.unary_min_length hq hp)
theorem len_addZ_le (c e : ℤ) : len (c + e) ≤ len c + len e := by
  have h : Nat.size (c + e).natAbs ≤ Nat.size c.natAbs + Nat.size e.natAbs + 1 := by
    rw [Nat.size_le]
    have h0 := Int.natAbs_add_le c e
    have h1 := Nat.lt_size_self c.natAbs
    have h2 := Nat.lt_size_self e.natAbs
    have h3 : 2 ^ Nat.size c.natAbs ≤ 2 ^ (Nat.size c.natAbs + Nat.size e.natAbs) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 2 ^ Nat.size e.natAbs ≤ 2 ^ (Nat.size c.natAbs + Nat.size e.natAbs) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ]
    omega
  simp only [len_int]; omega
theorem len_mulZ_le (c e : ℤ) : len (c * e) ≤ len c + len e := by
  have h : Nat.size (c * e).natAbs ≤ Nat.size c.natAbs + Nat.size e.natAbs := by
    rw [Int.natAbs_mul, Nat.size_le, pow_add]
    exact Nat.mul_lt_mul'' (Nat.lt_size_self _) (Nat.lt_size_self _)
  simp only [len_int]; omega
@[fun_prop] theorem sumZ_polyT {l : α → List ℤ} (hl : PolyT l) : PolyT fun x => (l x).sum := by
  obtain ⟨t, ht, -, hlen⟩ := PolyT.len_bound hl
  have h : PolyT (fun x => (l x).foldl (fun c e => c + e) 0) := by
    refine PolyT.foldl_add (g := fun _ c e => c + e) hl (by fun_prop) (by fun_prop) ⟨t, ht, fun x c e he => ?_⟩
    exact (len_addZ_le c e).trans (Nat.add_le_add_left ((len_le_of_mem he).trans (hlen x)) _)
  exact h.congr fun x => by rw [List.sum_eq_foldl]
@[fun_prop] theorem prodZ_polyT {l : α → List ℤ} (hl : PolyT l) : PolyT fun x => (l x).prod := by
  obtain ⟨t, ht, -, hlen⟩ := PolyT.len_bound hl
  have h : PolyT (fun x => (l x).foldl (fun c e => c * e) 1) := by
    refine PolyT.foldl_add (g := fun _ c e => c * e) hl (by fun_prop) (by fun_prop) ⟨t, ht, fun x c e he => ?_⟩
    exact (len_mulZ_le c e).trans (Nat.add_le_add_left ((len_le_of_mem he).trans (hlen x)) _)
  exact h.congr fun x => by rw [List.prod_eq_foldl]
@[fun_prop] theorem sumF_polyT {N : α → ℕ} {pad : α → U} {f : α → ℕ → ℤ} (hN : PolyT N) (hp : PolyT pad)
    (hf : PolyT fun p : α × ℕ => f p.1 p.2) : PolyT fun x => sumF (N x) (pad x) (f x) := by
  unfold sumF
  have hr : PolyT fun x => List.range (min (N x) (pad x).length) := PolyT.range (PolyT.unary_min_length hN hp)
  obtain ⟨b, hb, hbl⟩ := PolyT.len_bound_mem hf hr
  refine PolyT.foldl_add (g := fun x acc y => acc + f x y) hr (by fun_prop) ?_ ⟨b, hb, fun x c e he => ?_⟩
  · have : PolyT fun p : α × ℤ × ℕ => f p.1 p.2.2 :=
      PolyT.comp (g := fun p : α × ℤ × ℕ => (p.1, p.2.2)) hf (by fun_prop)
    fun_prop
  · have := len_addZ_le c (f x e)
    have := hbl x e he
    omega
@[fun_prop] theorem prodL_polyT {n : α → ℕ} {f : α → ℕ → ℤ} (hn : Unary n)
    (hf : PolyT fun p : α × ℕ => f p.1 p.2) : PolyT fun x => prodL (n x) (f x) := by
  unfold prodL
  have hr : PolyT fun x => List.range (n x) := PolyT.range hn
  obtain ⟨b, hb, hbl⟩ := PolyT.len_bound_mem hf hr
  refine PolyT.foldl_add (g := fun x acc y => acc * f x y) hr (by fun_prop) ?_ ⟨b, hb, fun x c e he => ?_⟩
  · have : PolyT fun p : α × ℤ × ℕ => f p.1 p.2.2 :=
      PolyT.comp (g := fun p : α × ℤ × ℕ => (p.1, p.2.2)) hf (by fun_prop)
    fun_prop
  · have := len_mulZ_le c (f x e)
    have := hbl x e he
    omega
instance : Meas ℕ := ⟨by
  have : PolyT fun n : ℕ => 3 * Nat.size n + 2 := by fun_prop
  exact this.congr fun n => (len_nat n).symm⟩
instance : Meas ℤ := ⟨by
  have : PolyT fun z : ℤ => 3 * Nat.size z.natAbs + 5 := by fun_prop
  exact this.congr fun z => (len_int z).symm⟩
instance : Meas Bool := ⟨(PolyT.const 1).congr fun _ => rfl⟩
instance : Meas Unit := ⟨(PolyT.const 2).congr fun _ => rfl⟩
instance [Meas α] [Meas β] : Meas (α × β) := ⟨by
  have h1 := Meas.poly (α := α)
  have h2 := Meas.poly (α := β)
  have : PolyT fun p : α × β => len p.1 + len p.2 + 2 := by fun_prop
  exact this.congr fun p => (len_pair p.1 p.2).symm⟩
instance [Meas α] : Meas (List α) := ⟨by
  have h1 := Meas.poly (α := α)
  have : PolyT fun l : List α => (l.map fun a => len a + 2).sum + 2 := by fun_prop
  exact this.congr fun l => (len_list l).symm⟩
end PaddedDescent.F


