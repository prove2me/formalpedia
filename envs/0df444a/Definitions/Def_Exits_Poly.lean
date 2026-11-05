-- Prove2me | Definitions.Def_Exits_Poly
-- name    : Exits_Poly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:51:21.776771+00:00
-- url     : https://prove2.me/theorems/27156715-ab1f-444e-a5e0-bd9272814ad7
-- title:
--   Poly
-- statement:
--   Definitions and structural lemmas for Poly, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Poly.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_Defs
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Walk
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_div_pow
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_idxOf
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_mod
import Theorems.Thm_Groundwork_PolyT_mul
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
import Theorems.Thm_Groundwork_Unary_comp
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
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
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
namespace Exits
open Groundwork Groundwork.Stepped
variable {α β γ τ ν : Type}
section foldUntil
variable [Enc τ] [Enc γ] [Enc α] [Enc β] {start : α → Option τ} {nxt : τ → Option τ} {M : Stepped τ β} [IsPolyT M] {g : γ → τ → β → γ} {stop : γ → Bool} {c₀ : α → γ}
theorem IsPolyT.foldUntil_step (hn : PolyT nxt) (hg : PolyT fun p : γ × τ × β => g p.1 p.2.1 p.2.2) (hst : PolyT stop) :
    PolyT (fun s : (τ × γ × M.σ) ⊕ γ => match s with
      | .inl p => match M.out p.2.2 with
        | some b => foldGo M (g p.2.1 p.1 b) (if stop (g p.2.1 p.1 b) then none else nxt p.1)
        | none => .inl (p.1, p.2.1, M.step p.2.2)
      | .inr c => .inr c) := by
  have h1 := IsPolyT.step (M := M)
  have h2 := IsPolyT.out (M := M)
  have hg' : PolyT fun q : (τ × γ × M.σ) × β => g q.1.2.1 q.1.1 q.2 := PolyT.comp (g := fun q : (τ × γ × M.σ) × β => (q.1.2.1, q.1.1, q.2)) hg (by fun_prop)
  have hsg : PolyT fun q : (τ × γ × M.σ) × β => stop (g q.1.2.1 q.1.1 q.2) := PolyT.comp hst hg'
  have hnx : PolyT fun q : (τ × γ × M.σ) × β => if stop (g q.1.2.1 q.1.1 q.2) then none else nxt q.1.1 := PolyT.ite' (PolyT.decide_eq_true hsg) (by fun_prop) (by fun_prop)
  have h3 : PolyT fun q : (τ × γ × M.σ) × β => foldGo M (g q.1.2.1 q.1.1 q.2) (if stop (g q.1.2.1 q.1.1 q.2) then none else nxt q.1.1) :=
    PolyT.comp (g := fun q : (τ × γ × M.σ) × β => (g q.1.2.1 q.1.1 q.2, if stop (g q.1.2.1 q.1.1 q.2) then none else nxt q.1.1)) (IsPolyT.foldGo_poly (M := M) (γ := γ)) (PolyT.prodMk hg' hnx)
  have h4 : PolyT fun p : τ × γ × M.σ => (M.out p.2.2).elim (.inl (p.1, p.2.1, M.step p.2.2) : (τ × γ × M.σ) ⊕ γ)
      fun b => foldGo M (g p.2.1 p.1 b) (if stop (g p.2.1 p.1 b) then none else nxt p.1) :=
    PolyT.optionElim (by fun_prop) (by fun_prop) h3
  have h5 : PolyT fun s : (τ × γ × M.σ) ⊕ γ => s.elim
      (fun p => (M.out p.2.2).elim (.inl (p.1, p.2.1, M.step p.2.2) : (τ × γ × M.σ) ⊕ γ)
        fun b => foldGo M (g p.2.1 p.1 b) (if stop (g p.2.1 p.1 b) then none else nxt p.1)) fun c => .inr c :=
    PolyT.sumElim (by fun_prop) (PolyT.comp (g := fun q : ((τ × γ × M.σ) ⊕ γ) × (τ × γ × M.σ) => q.2) h4 (by fun_prop)) (by fun_prop)
  refine h5.congr fun s => ?_
  rcases s with p | c
  · simp only [Sum.elim_inl]
    cases M.out p.2.2 <;> rfl
  · rfl
variable [HasSize τ] [HasSize γ] [Carried τ] [Carried γ]
@[instance_reducible] def IsPolyT.foldUntil (hs : PolyT start) (hn : PolyT nxt) (hg : PolyT fun p : γ × τ × β => g p.1 p.2.1 p.2.2) (hst : PolyT stop) (hc : PolyT c₀) :
    IsPolyT (foldUntil start nxt M g stop c₀) where
  enc := (inferInstance : Enc ((τ × γ × M.σ) ⊕ γ))
  carried := (inferInstance : Carried ((τ × γ × M.σ) ⊕ γ))
  init := IsPolyT.foldWhile_init hs hc
  step := IsPolyT.foldUntil_step hn hg hst
  out := IsPolyT.foldWhile_out
end foldUntil
@[instance_reducible] def IsPolyT.firstUntil [Enc α] [HasSize α] [Carried α] [Enc β] {N : α → ℕ} {M : Stepped (α × ℕ) β} [IsPolyT M] {p : β → Bool} (hN : PolyT N) (hp : PolyT p) :
    IsPolyT (firstUntil N M p) :=
  IsPolyT.foldUntil (IsPolyT.rangeStart_poly hN) (IsPolyT.rangeNext_poly hN)
    ((by fun_prop : PolyT fun q : Option ℕ × (α × ℕ) × β => q.1.elim (if p q.2.2 = true then some q.2.1.2 else none) fun i => some i).congr
      fun q => by rcases q with ⟨_ | i, y, b⟩ <;> rfl)
    (PolyT.optionIsSome PolyT.id') (by unfold noneC; fun_prop)
@[instance_reducible] def IsPolyT.walkUntil [Enc ν] [HasSize ν] [Carried ν] [Enc α] {step : ν → Option (ν × ν)} {root : α → ν} {T : Stepped ν Bool} [IsPolyT T] (hs : PolyT step) (hr : PolyT root) :
    IsPolyT (walkUntil step root T) :=
  haveI := IsPolyT.guard (T := T) (d := false) (IsPolyT.walkSel_polyT hs)
  IsPolyT.foldUntil (by fun_prop) (IsPolyT.walkNext_polyT hs) (by fun_prop) PolyT.id' (by fun_prop)
end Exits


