-- Prove2me | Definitions.Def_ToTuring_Poly_Comb
-- name    : ToTuring_Poly_Comb
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:50:19.739717+00:00
-- url     : https://prove2.me/theorems/44217eb7-067d-4ae5-bb32-ec9530935503
-- title:
--   Comb
-- statement:
--   Definitions and structural lemmas for Comb, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Comb.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_StepMachines_Prog_Comb
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
import Theorems.Thm_Groundwork_Unary_const
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
variable {α α₁ α₂ β γ δ ι : Type}
section branch
variable [Enc α] [Enc α₁] [Enc α₂] [Enc β] {sel : α → α₁ ⊕ α₂} {M₁ : Stepped α₁ β} {M₂ : Stepped α₂ β} [IsPolyT M₁]
  [IsPolyT M₂]
theorem branch_init (hs : PolyT sel) : PolyT (fun a : α => match sel a with
    | .inl x => (.inl (M₁.init x) : M₁.σ ⊕ M₂.σ) | .inr y => .inr (M₂.init y)) := by
  have := IsPolyT.init (M := M₁); have := IsPolyT.init (M := M₂)
  refine (by fun_prop : PolyT fun a : α => (sel a).elim (fun x => (.inl (M₁.init x) : M₁.σ ⊕ M₂.σ))
    fun y => .inr (M₂.init y)).congr fun a => ?_
  cases sel a <;> rfl
theorem branch_step : PolyT (fun s : M₁.σ ⊕ M₂.σ => match s with
    | .inl s => (.inl (M₁.step s) : M₁.σ ⊕ M₂.σ) | .inr s => .inr (M₂.step s)) := by
  have := IsPolyT.step (M := M₁); have := IsPolyT.step (M := M₂)
  exact (by fun_prop : PolyT fun s : M₁.σ ⊕ M₂.σ => s.elim (fun s => (.inl (M₁.step s) : M₁.σ ⊕ M₂.σ))
    fun s => .inr (M₂.step s)).congr fun s => by cases s <;> rfl
theorem branch_out : PolyT (fun s : M₁.σ ⊕ M₂.σ => match s with | .inl s => M₁.out s | .inr s => M₂.out s) := by
  have := IsPolyT.out (M := M₁); have := IsPolyT.out (M := M₂)
  exact (by fun_prop : PolyT fun s : M₁.σ ⊕ M₂.σ => s.elim (fun s => M₁.out s) fun s => M₂.out s).congr
    fun s => by cases s <;> rfl
@[instance_reducible] def branch (hs : PolyT sel) : IsPolyT (branch sel M₁ M₂) where
  enc := (inferInstance : Enc (M₁.σ ⊕ M₂.σ))
  carried := (inferInstance : Carried (M₁.σ ⊕ M₂.σ))
  init := branch_init hs
  step := branch_step
  out := branch_out
end branch
section ite
variable [Enc α] [Enc β] {p : α → Bool} {M N : Stepped α β} [IsPolyT M] [IsPolyT N]
theorem iteSel_poly (hp : PolyT p) : PolyT (iteSel p) := by unfold iteSel; fun_prop
@[instance_reducible] def ite (hp : PolyT p) : IsPolyT (ite p M N) := branch (iteSel_poly hp)
end ite
section const
variable [HasSize α] [HasSize β] [Enc α] [Carried α] [Enc β] [Carried β]
@[instance_reducible] def const (b : β) : IsPolyT (const b : Stepped α β) := ofFun (by unfold Function.const; fun_prop)
end const
section optBind
variable [HasSize α] [HasSize β] [Enc α] [Carried α] [Enc β] [Carried β] [Enc ι] {M : Stepped α (Option ι)}
  {N : Stepped (α × ι) β} {dflt : α → β} [IsPolyT M] [IsPolyT N]
omit [HasSize α] [Carried α] in
theorem optSel_poly : PolyT (optSel : α × Option ι → (α × ι) ⊕ α) :=
  (by fun_prop : PolyT fun x : α × Option ι => x.2.elim (.inr x.1 : (α × ι) ⊕ α) fun i => .inl (x.1, i)).congr
    fun x => by rcases x with ⟨a, _ | i⟩ <;> rfl
@[instance_reducible] def optBind (hd : PolyT dflt) : IsPolyT (optBind M N dflt) :=
  haveI := ofFun hd
  haveI : IsPolyT (Stepped.branch optSel N (Stepped.ofFun dflt)) := branch optSel_poly
  bind
end optBind
section both
variable [HasSize α] [HasSize β] [Enc α] [Carried α] [Enc β] [Carried β] [Enc γ] {M : Stepped α β} {N : Stepped α γ}
  [IsPolyT M] [IsPolyT N]
omit [HasSize α] [HasSize β] [Carried α] [Carried β] in
theorem both_init : PolyT (fun a : α => (.inl (a, M.init a) : (α × M.σ) ⊕ (β × N.σ))) := by
  have := IsPolyT.init (M := M); fun_prop
omit [HasSize α] [HasSize β] [Carried α] [Carried β] in
theorem both_step : PolyT (fun s : (α × M.σ) ⊕ (β × N.σ) => match s with
    | .inl p => match M.out p.2 with
      | some b => (.inr (b, N.init p.1) : (α × M.σ) ⊕ (β × N.σ))
      | none => .inl (p.1, M.step p.2)
    | .inr p => .inr (p.1, N.step p.2)) := by
  have := IsPolyT.step (M := M); have := IsPolyT.out (M := M)
  have := IsPolyT.init (M := N); have := IsPolyT.step (M := N)
  refine (by fun_prop : PolyT fun s : (α × M.σ) ⊕ (β × N.σ) => s.elim
    (fun p => (M.out p.2).elim (.inl (p.1, M.step p.2) : (α × M.σ) ⊕ (β × N.σ)) fun b => .inr (b, N.init p.1))
    fun p => .inr (p.1, N.step p.2)).congr fun s => ?_
  rcases s with p | s
  · simp only [Sum.elim_inl]
    cases M.out p.2 <;> rfl
  · rfl
omit [HasSize α] [HasSize β] [Carried α] [Carried β] in
theorem both_out : PolyT (fun s : (α × M.σ) ⊕ (β × N.σ) => match s with
    | .inl _ => none | .inr p => (N.out p.2).map fun c => (p.1, c)) := by
  have := IsPolyT.out (M := N)
  exact (by fun_prop : PolyT fun s : (α × M.σ) ⊕ (β × N.σ) => s.elim (fun _ => none)
    fun p => (N.out p.2).map fun c => (p.1, c)).congr fun s => by cases s <;> rfl
@[instance_reducible] def both : IsPolyT (both M N) where
  enc := (inferInstance : Enc ((α × M.σ) ⊕ (β × N.σ)))
  carried := (inferInstance : Carried ((α × M.σ) ⊕ (β × N.σ)))
  init := both_init
  step := both_step
  out := both_out
@[instance_reducible] def map2 [Enc δ] {f : β → γ → δ} (hf : PolyT fun p : β × γ => f p.1 p.2) : IsPolyT (map2 f M N) :=
  haveI : IsPolyT (Stepped.both M N) := both
  mapOut (by unfold Function.uncurry; exact hf)
end both
section mul2
variable [HasSize α] [Enc α] [Carried α] {M N : Stepped α ℤ} [IsPolyT M] [IsPolyT N]
@[instance_reducible] def mul2 : IsPolyT (mul2 M N) := map2 (by change PolyT fun p : ℤ × ℤ => p.1 * p.2; fun_prop)
end mul2
end IsPolyT
end Groundwork


