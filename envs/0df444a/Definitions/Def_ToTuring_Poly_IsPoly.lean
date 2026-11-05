-- Prove2me | Definitions.Def_ToTuring_Poly_IsPoly
-- name    : ToTuring_Poly_IsPoly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:46:19.184233+00:00
-- url     : https://prove2.me/theorems/190b91dc-1903-46e2-a493-bfa25f304e7c
-- title:
--   Is Poly
-- statement:
--   Definitions and structural lemmas for Is Poly, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/IsPoly.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_StepMachines_Prog_Range
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
namespace Groundwork
namespace IsPolyT
open Stepped
variable {α β γ τ : Type}
section ofFun
variable [Enc α] [Enc β]
theorem ofFun_step {f : α → β} (hf : PolyT f) :
    PolyT (fun s : α ⊕ β => match s with | .inl a => (.inr (f a) : α ⊕ β) | .inr b => .inr b) :=
  (by fun_prop : PolyT fun s : α ⊕ β => s.elim (fun a => (.inr (f a) : α ⊕ β)) fun b => .inr b).congr
    fun s => by cases s <;> rfl
theorem ofFun_out : PolyT (fun s : α ⊕ β => match s with | .inl _ => none | .inr b => some b) :=
  (by fun_prop : PolyT fun s : α ⊕ β => s.elim (fun _ => none) fun b => some b).congr fun s => by cases s <;> rfl
theorem ofFun_init : PolyT (fun a : α => (.inl a : α ⊕ β)) := by fun_prop
variable [HasSize α] [HasSize β] [Carried α] [Carried β]
@[instance_reducible] def ofFun {f : α → β} (hf : PolyT f) : IsPolyT (ofFun f) where
  enc := (inferInstance : Enc (α ⊕ β))
  carried := (inferInstance : Carried (α ⊕ β))
  init := ofFun_init
  step := ofFun_step hf
  out := ofFun_out
end ofFun
section foldWhile
variable [Enc τ] [Enc γ] [Enc α] [Enc β] {start : α → Option τ} {nxt : τ → Option τ} {M : Stepped τ β} [IsPolyT M]
  {g : γ → τ → β → γ} {c₀ : α → γ}
theorem foldGo_poly : PolyT (fun p : γ × Option τ => foldGo M p.1 p.2) := by
  have := IsPolyT.init (M := M)
  exact (by fun_prop : PolyT fun p : γ × Option τ =>
    p.2.elim (.inr p.1 : (τ × γ × M.σ) ⊕ γ) fun x => .inl (x, p.1, M.init x)).congr fun p => by
      rcases p with ⟨c, _ | x⟩ <;> rfl
theorem foldWhile_init (hs : PolyT start) (hc : PolyT c₀) : PolyT (fun a => foldGo M (c₀ a) (start a)) :=
  PolyT.comp (g := fun a => (c₀ a, start a)) (foldGo_poly (M := M) (γ := γ)) (by fun_prop)
theorem foldWhile_step (hn : PolyT nxt) (hg : PolyT fun p : γ × τ × β => g p.1 p.2.1 p.2.2) :
    PolyT (fun s : (τ × γ × M.σ) ⊕ γ => match s with
      | .inl p => match M.out p.2.2 with
        | some b => foldGo M (g p.2.1 p.1 b) (nxt p.1)
        | none => .inl (p.1, p.2.1, M.step p.2.2)
      | .inr c => .inr c) := by
  have h1 := IsPolyT.step (M := M)
  have h2 := IsPolyT.out (M := M)
  have h3 : PolyT fun q : (τ × γ × M.σ) × β => foldGo M (g q.1.2.1 q.1.1 q.2) (nxt q.1.1) :=
    PolyT.comp (g := fun q : (τ × γ × M.σ) × β => (g q.1.2.1 q.1.1 q.2, nxt q.1.1)) (foldGo_poly (M := M) (γ := γ))
      (PolyT.prodMk (PolyT.comp (g := fun q : (τ × γ × M.σ) × β => (q.1.2.1, q.1.1, q.2)) hg (by fun_prop)) (by fun_prop))
  have h4 : PolyT fun p : τ × γ × M.σ => (M.out p.2.2).elim (.inl (p.1, p.2.1, M.step p.2.2) : (τ × γ × M.σ) ⊕ γ)
      fun b => foldGo M (g p.2.1 p.1 b) (nxt p.1) :=
    PolyT.optionElim (by fun_prop) (by fun_prop) h3
  have h5 : PolyT fun s : (τ × γ × M.σ) ⊕ γ => s.elim
      (fun p => (M.out p.2.2).elim (.inl (p.1, p.2.1, M.step p.2.2) : (τ × γ × M.σ) ⊕ γ)
        fun b => foldGo M (g p.2.1 p.1 b) (nxt p.1)) fun c => .inr c :=
    PolyT.sumElim (by fun_prop) (PolyT.comp (g := fun q : ((τ × γ × M.σ) ⊕ γ) × (τ × γ × M.σ) => q.2) h4 (by fun_prop))
      (by fun_prop)
  refine h5.congr fun s => ?_
  rcases s with p | c
  · simp only [Sum.elim_inl]
    cases M.out p.2.2 <;> rfl
  · rfl
theorem foldWhile_out : PolyT (fun s : (τ × γ × M.σ) ⊕ γ => match s with | .inl _ => none | .inr c => some c) :=
  (by fun_prop : PolyT fun s : (τ × γ × M.σ) ⊕ γ => s.elim (fun _ => none) fun c => some c).congr
    fun s => by cases s <;> rfl
variable [HasSize τ] [HasSize γ] [Carried τ] [Carried γ]
@[instance_reducible] def foldWhile (hs : PolyT start) (hn : PolyT nxt) (hg : PolyT fun p : γ × τ × β => g p.1 p.2.1 p.2.2)
    (hc : PolyT c₀) : IsPolyT (foldWhile start nxt M g c₀) where
  enc := (inferInstance : Enc ((τ × γ × M.σ) ⊕ γ))
  carried := (inferInstance : Carried ((τ × γ × M.σ) ⊕ γ))
  init := foldWhile_init hs hc
  step := foldWhile_step hn hg
  out := foldWhile_out
end foldWhile
end IsPolyT
end Groundwork


