-- Prove2me | Definitions.Def_QueryMachines_Poly
-- name    : QueryMachines_Poly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:56:07.513191+00:00
-- url     : https://prove2.me/theorems/1abb17e8-55ae-41aa-8330-e85c7cf564e7
-- title:
--   Poly
-- statement:
--   Definitions and structural lemmas for Poly, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Poly.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Comb
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Mathlib.Tactic
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PB_comp
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
import Theorems.Thm_Groundwork_Prog_NetE_zA_polyT
import Theorems.Thm_Groundwork_Prog_NetE_zAt_polyT
import Theorems.Thm_Groundwork_Prog_NetE_zOf_polyT
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
import Theorems.Thm_Groundwork_TM_update_withIO
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_block_polyT
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_query0_polyT
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
import Theorems.Thm_Groundwork_tri_polyT
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
import Theorems.Thm_QueryMachines_QueryMachine_close_bind
import Theorems.Thm_QueryMachines_QueryMachine_close_both
import Theorems.Thm_QueryMachines_QueryMachine_close_branch
import Theorems.Thm_QueryMachines_QueryMachine_close_const
import Theorems.Thm_QueryMachines_QueryMachine_close_foldRange
import Theorems.Thm_QueryMachines_QueryMachine_close_foldWhile
import Theorems.Thm_QueryMachines_QueryMachine_close_gated
import Theorems.Thm_QueryMachines_QueryMachine_close_ite
import Theorems.Thm_QueryMachines_QueryMachine_close_lift
import Theorems.Thm_QueryMachines_QueryMachine_close_mapAsk
import Theorems.Thm_QueryMachines_QueryMachine_close_mapIn
import Theorems.Thm_QueryMachines_QueryMachine_close_mapOut
import Theorems.Thm_QueryMachines_QueryMachine_close_optBind
import Theorems.Thm_QueryMachines_QueryMachine_close_prodRange
import Theorems.Thm_QueryMachines_QueryMachine_close_query
import Theorems.Thm_QueryMachines_QueryMachine_close_subst
import Theorems.Thm_QueryMachines_QueryMachine_close_sumRange
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
attribute [local fun_prop] Groundwork.block_polyT
attribute [local fun_prop] Groundwork.query0_polyT
attribute [local fun_prop] Groundwork.tri_polyT
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
attribute [local simp] Groundwork.Host.upd_none
attribute [local simp] Groundwork.Host.withIO_none
attribute [local simp] Groundwork.Host.withIO_some
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
attribute [local simp] Groundwork.TM.update_withIO
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
attribute [local simp] QueryMachines.QueryMachine.close_bind
attribute [local simp] QueryMachines.QueryMachine.close_both
attribute [local simp] QueryMachines.QueryMachine.close_branch
attribute [local simp] QueryMachines.QueryMachine.close_const
attribute [local simp] QueryMachines.QueryMachine.close_foldRange
attribute [local simp] QueryMachines.QueryMachine.close_foldWhile
attribute [local simp] QueryMachines.QueryMachine.close_gated
attribute [local simp] QueryMachines.QueryMachine.close_ite
attribute [local simp] QueryMachines.QueryMachine.close_lift
attribute [local simp] QueryMachines.QueryMachine.close_mapAsk
attribute [local simp] QueryMachines.QueryMachine.close_mapIn
attribute [local simp] QueryMachines.QueryMachine.close_mapOut
attribute [local simp] QueryMachines.QueryMachine.close_optBind
attribute [local simp] QueryMachines.QueryMachine.close_prodRange
attribute [local simp] QueryMachines.QueryMachine.close_query
attribute [local simp] QueryMachines.QueryMachine.close_subst
attribute [local simp] QueryMachines.QueryMachine.close_sumRange


set_option autoImplicit false
section
section
namespace QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' A' C α α₁ α₂ β γ δ ι τ : Type}
namespace IsPolyQ
@[instance_reducible] instance under [Enc Q] [Enc A] [Enc α] [Enc β] (M : QueryMachine Q A α β) [h : IsPolyQ M] : IsPolyT M.toStepped where
  enc := h.enc
  carried := h.carried
  init := h.init
  step := h.step
  out := h.out
section lift
variable [Enc Q] [Enc A] [Enc α] [Enc β]
@[instance_reducible] def lift (R : Stepped α β) [h : IsPolyT R] : IsPolyQ (QueryMachine.lift R : QueryMachine Q A α β) where
  enc := h.enc
  carried := h.carried
  init := h.init
  step := h.step
  out := h.out
  ask := (by fun_prop : PolyT fun _ : R.σ => (none : Option Q))
  resume := (by fun_prop : PolyT fun p : R.σ × A => p.1)
end lift
section query
variable [Enc Q] [Enc A] [Enc α] [HasSize α] [HasSize A] [Carried α] [Carried A]
@[instance_reducible] def query {h : α → Q} (hh : PolyT h) : IsPolyQ (QueryMachine.query h : QueryMachine Q A α A) where
  enc := (inferInstance : Enc (α ⊕ A))
  carried := (inferInstance : Carried (α ⊕ A))
  init := (by fun_prop : PolyT fun a : α => (.inl a : α ⊕ A))
  step := (by fun_prop : PolyT fun s : α ⊕ A => s)
  out := (IsPolyT.ofFun_out (α := α) (β := A)).congr fun s => by cases s <;> rfl
  ask := (by fun_prop : PolyT fun s : α ⊕ A => s.elim (fun a => some (h a)) fun _ => none).congr fun s => by cases s <;> rfl
  resume := (by fun_prop : PolyT fun p : (α ⊕ A) × A => (.inr p.2 : α ⊕ A))
end query
section maps
variable [Enc Q] [Enc Q'] [Enc A] [Enc α] [Enc β] [Enc γ]
@[instance_reducible] def mapAsk {h : Q → Q'} (hh : PolyT h) (M : QueryMachine Q A α β) [i : IsPolyQ M] : IsPolyQ (QueryMachine.mapAsk h M) where
  enc := i.enc
  carried := i.carried
  init := i.init
  step := i.step
  out := i.out
  ask := by
    have := i.ask
    exact (by fun_prop : PolyT fun s : M.σ => (M.ask s).map h)
  resume := i.resume
@[instance_reducible] def mapIn {g : α → β} (hg : PolyT g) (M : QueryMachine Q A β γ) [i : IsPolyQ M] : IsPolyQ (QueryMachine.mapIn g M) where
  enc := i.enc
  carried := i.carried
  init := IsPolyT.mapIn_init (M := M.toStepped) hg
  step := i.step
  out := i.out
  ask := i.ask
  resume := i.resume
@[instance_reducible] def mapOut (M : QueryMachine Q A α β) [i : IsPolyQ M] {g : β → γ} (hg : PolyT g) : IsPolyQ (QueryMachine.mapOut M g) where
  enc := i.enc
  carried := i.carried
  init := i.init
  step := i.step
  out := IsPolyT.mapOut_out (M := M.toStepped) hg
  ask := i.ask
  resume := i.resume
end maps
section bind
variable [Enc Q] [Enc A] [Enc α] [Enc β] [Enc γ] [HasSize α] [Carried α] (M : QueryMachine Q A α β) (N : QueryMachine Q A (α × β) γ) [IsPolyQ M] [IsPolyQ N]
@[instance_reducible] def bind : IsPolyQ (QueryMachine.bind M N) where
  enc := (inferInstance : Enc ((α × M.σ) ⊕ N.σ))
  carried := (inferInstance : Carried ((α × M.σ) ⊕ N.σ))
  init := IsPolyT.bind_init (M := M.toStepped) (N := N.toStepped)
  step := IsPolyT.bind_step (M := M.toStepped) (N := N.toStepped)
  out := IsPolyT.bind_out (M := M.toStepped) (N := N.toStepped)
  ask := by
    have h1 := IsPolyQ.out (M := M); have h2 := IsPolyQ.ask (M := M); have h3 := IsPolyQ.ask (M := N)
    refine (by fun_prop : PolyT fun s : (α × M.σ) ⊕ N.σ => s.elim (fun p => (M.out p.2).elim (M.ask p.2) fun _ => none) fun s => N.ask s).congr fun s => ?_
    rcases s with p | s
    · change _ = (match M.out p.2 with | some _ => none | none => M.ask p.2)
      simp only [Sum.elim_inl]
      cases M.out p.2 <;> rfl
    · rfl
  resume := by
    have h1 : PolyT fun q : (((α × M.σ) ⊕ N.σ) × A) × (α × M.σ) => M.resume q.2.2 q.1.2 :=
      PolyT.comp (g := fun q : (((α × M.σ) ⊕ N.σ) × A) × (α × M.σ) => (q.2.2, q.1.2)) (IsPolyQ.resume (M := M)) (by fun_prop)
    have h2 : PolyT fun q : (((α × M.σ) ⊕ N.σ) × A) × N.σ => N.resume q.2 q.1.2 :=
      PolyT.comp (g := fun q : (((α × M.σ) ⊕ N.σ) × A) × N.σ => (q.2, q.1.2)) (IsPolyQ.resume (M := N)) (by fun_prop)
    refine (PolyT.sumElim (s := fun q : ((α × M.σ) ⊕ N.σ) × A => q.1) (f := fun q p => (.inl (p.1, M.resume p.2 q.2) : (α × M.σ) ⊕ N.σ))
      (g := fun q s => .inr (N.resume s q.2)) (by fun_prop) (by fun_prop) (by fun_prop)).congr fun q => ?_
    rcases q with ⟨p | s, v⟩ <;> rfl
end bind
section foldWhile
variable [Enc Q] [Enc A] [Enc α] [Enc β] [Enc γ] [Enc τ] [HasSize τ] [HasSize γ] [Carried τ] [Carried γ] {start : α → Option τ} {nxt : τ → Option τ} (M : QueryMachine Q A τ β) [IsPolyQ M]
  {g : γ → τ → β → γ} {c₀ : α → γ}
@[instance_reducible] def foldWhile (hs : PolyT start) (hn : PolyT nxt) (hg : PolyT fun p : γ × τ × β => g p.1 p.2.1 p.2.2) (hc : PolyT c₀) : IsPolyQ (QueryMachine.foldWhile start nxt M g c₀) where
  enc := (inferInstance : Enc ((τ × γ × M.σ) ⊕ γ))
  carried := (inferInstance : Carried ((τ × γ × M.σ) ⊕ γ))
  init := IsPolyT.foldWhile_init (M := M.toStepped) hs hc
  step := IsPolyT.foldWhile_step (M := M.toStepped) hn hg
  out := IsPolyT.foldWhile_out (M := M.toStepped)
  ask := by
    have h1 := IsPolyQ.out (M := M); have h2 := IsPolyQ.ask (M := M)
    refine (by fun_prop : PolyT fun s : (τ × γ × M.σ) ⊕ γ => s.elim (fun p => (M.out p.2.2).elim (M.ask p.2.2) fun _ => none) fun _ => none).congr fun s => ?_
    rcases s with p | s
    · change _ = (match M.out p.2.2 with | some _ => none | none => M.ask p.2.2)
      simp only [Sum.elim_inl]
      cases M.out p.2.2 <;> rfl
    · rfl
  resume := by
    have h1 : PolyT fun q : (((τ × γ × M.σ) ⊕ γ) × A) × (τ × γ × M.σ) => M.resume q.2.2.2 q.1.2 :=
      PolyT.comp (g := fun q : (((τ × γ × M.σ) ⊕ γ) × A) × (τ × γ × M.σ) => (q.2.2.2, q.1.2)) (IsPolyQ.resume (M := M)) (by fun_prop)
    refine (PolyT.sumElim (s := fun q : ((τ × γ × M.σ) ⊕ γ) × A => q.1) (f := fun q p => (.inl (p.1, p.2.1, M.resume p.2.2 q.2) : (τ × γ × M.σ) ⊕ γ))
      (g := fun _ c => .inr c) (by fun_prop) (by fun_prop) (by fun_prop)).congr fun q => ?_
    rcases q with ⟨p | s, v⟩ <;> rfl
end foldWhile
section branch
variable [Enc Q] [Enc A] [Enc α] [Enc α₁] [Enc α₂] [Enc β] {sel : α → α₁ ⊕ α₂} (M₁ : QueryMachine Q A α₁ β) (M₂ : QueryMachine Q A α₂ β) [IsPolyQ M₁] [IsPolyQ M₂]
@[instance_reducible] def branch (hs : PolyT sel) : IsPolyQ (QueryMachine.branch sel M₁ M₂) where
  enc := (inferInstance : Enc (M₁.σ ⊕ M₂.σ))
  carried := (inferInstance : Carried (M₁.σ ⊕ M₂.σ))
  init := IsPolyT.branch_init (M₁ := M₁.toStepped) (M₂ := M₂.toStepped) hs
  step := IsPolyT.branch_step (M₁ := M₁.toStepped) (M₂ := M₂.toStepped)
  out := IsPolyT.branch_out (M₁ := M₁.toStepped) (M₂ := M₂.toStepped)
  ask := by
    have h1 := IsPolyQ.ask (M := M₁); have h2 := IsPolyQ.ask (M := M₂)
    exact (by fun_prop : PolyT fun s : M₁.σ ⊕ M₂.σ => s.elim (fun s => M₁.ask s) fun s => M₂.ask s).congr fun s => by cases s <;> rfl
  resume := by
    have h1 : PolyT fun q : ((M₁.σ ⊕ M₂.σ) × A) × M₁.σ => M₁.resume q.2 q.1.2 :=
      PolyT.comp (g := fun q : ((M₁.σ ⊕ M₂.σ) × A) × M₁.σ => (q.2, q.1.2)) (IsPolyQ.resume (M := M₁)) (by fun_prop)
    have h2 : PolyT fun q : ((M₁.σ ⊕ M₂.σ) × A) × M₂.σ => M₂.resume q.2 q.1.2 :=
      PolyT.comp (g := fun q : ((M₁.σ ⊕ M₂.σ) × A) × M₂.σ => (q.2, q.1.2)) (IsPolyQ.resume (M := M₂)) (by fun_prop)
    refine (PolyT.sumElim (s := fun q : (M₁.σ ⊕ M₂.σ) × A => q.1) (f := fun q s => (.inl (M₁.resume s q.2) : M₁.σ ⊕ M₂.σ))
      (g := fun q s => .inr (M₂.resume s q.2)) (by fun_prop) (by fun_prop) (by fun_prop)).congr fun q => ?_
    rcases q with ⟨p | s, v⟩ <;> rfl
end branch
section both
variable [Enc Q] [Enc A] [Enc α] [Enc β] [Enc γ] [HasSize α] [HasSize β] [Carried α] [Carried β] (M : QueryMachine Q A α β) (N : QueryMachine Q A α γ) [IsPolyQ M] [IsPolyQ N]
@[instance_reducible] def both : IsPolyQ (QueryMachine.both M N) where
  enc := (inferInstance : Enc ((α × M.σ) ⊕ (β × N.σ)))
  carried := (inferInstance : Carried ((α × M.σ) ⊕ (β × N.σ)))
  init := IsPolyT.both_init (M := M.toStepped) (N := N.toStepped)
  step := IsPolyT.both_step (M := M.toStepped) (N := N.toStepped)
  out := IsPolyT.both_out (M := M.toStepped) (N := N.toStepped)
  ask := by
    have h1 := IsPolyQ.out (M := M); have h2 := IsPolyQ.ask (M := M); have h3 := IsPolyQ.ask (M := N)
    refine (by fun_prop : PolyT fun s : (α × M.σ) ⊕ (β × N.σ) => s.elim (fun p => (M.out p.2).elim (M.ask p.2) fun _ => none) fun p => N.ask p.2).congr fun s => ?_
    rcases s with p | s
    · change _ = (match M.out p.2 with | some _ => none | none => M.ask p.2)
      simp only [Sum.elim_inl]
      cases M.out p.2 <;> rfl
    · rfl
  resume := by
    have h1 : PolyT fun q : (((α × M.σ) ⊕ (β × N.σ)) × A) × (α × M.σ) => M.resume q.2.2 q.1.2 :=
      PolyT.comp (g := fun q : (((α × M.σ) ⊕ (β × N.σ)) × A) × (α × M.σ) => (q.2.2, q.1.2)) (IsPolyQ.resume (M := M)) (by fun_prop)
    have h2 : PolyT fun q : (((α × M.σ) ⊕ (β × N.σ)) × A) × (β × N.σ) => N.resume q.2.2 q.1.2 :=
      PolyT.comp (g := fun q : (((α × M.σ) ⊕ (β × N.σ)) × A) × (β × N.σ) => (q.2.2, q.1.2)) (IsPolyQ.resume (M := N)) (by fun_prop)
    refine (PolyT.sumElim (s := fun q : ((α × M.σ) ⊕ (β × N.σ)) × A => q.1) (f := fun q p => (.inl (p.1, M.resume p.2 q.2) : (α × M.σ) ⊕ (β × N.σ)))
      (g := fun q p => .inr (p.1, N.resume p.2 q.2)) (by fun_prop) (by fun_prop) (by fun_prop)).congr fun q => ?_
    rcases q with ⟨p | s, v⟩ <;> rfl
end both
section derived
variable [Enc Q] [Enc A] [Enc α] [Enc β]
@[instance_reducible] def ite {p : α → Bool} (hp : PolyT p) (M N : QueryMachine Q A α β) [IsPolyQ M] [IsPolyQ N] : IsPolyQ (QueryMachine.ite p M N) := branch M N (IsPolyT.iteSel_poly hp)
@[instance_reducible] def const [HasSize α] [HasSize β] [Carried α] [Carried β] (b : β) : IsPolyQ (QueryMachine.const b : QueryMachine Q A α β) :=
  haveI := IsPolyT.const (α := α) b
  lift (Stepped.const b)
@[instance_reducible] def optBind [HasSize α] [HasSize β] [Carried α] [Carried β] [Enc ι] (M : QueryMachine Q A α (Option ι)) (N : QueryMachine Q A (α × ι) β) [IsPolyQ M] [IsPolyQ N] {dflt : α → β}
    (hd : PolyT dflt) : IsPolyQ (QueryMachine.optBind M N dflt) :=
  haveI := IsPolyT.ofFun hd
  haveI : IsPolyQ (QueryMachine.lift (Stepped.ofFun dflt) : QueryMachine Q A α β) := lift _
  haveI : IsPolyQ (QueryMachine.branch Stepped.optSel N (QueryMachine.lift (Stepped.ofFun dflt))) := branch _ _ IsPolyT.optSel_poly
  bind _ _
@[instance_reducible] def foldRange [HasSize α] [Carried α] [HasSize γ] [Enc γ] [Carried γ] {N : α → ℕ} (M : QueryMachine Q A (α × ℕ) β) [IsPolyQ M] {g : γ → ℕ → β → γ} {c₀ : α → γ}
    (hN : PolyT N) (hg : PolyT fun p : γ × ℕ × β => g p.1 p.2.1 p.2.2) (hc : PolyT c₀) : IsPolyQ (QueryMachine.foldRange N M g c₀) :=
  foldWhile M (IsPolyT.rangeStart_poly hN) (IsPolyT.rangeNext_poly hN)
    (by unfold Stepped.rangeG; exact PolyT.comp (g := fun p : γ × (α × ℕ) × β => (p.1, p.2.1.2, p.2.2)) hg (by fun_prop)) hc
@[instance_reducible] def sumRange [HasSize α] [Carried α] {N : α → ℕ} (M : QueryMachine Q A (α × ℕ) ℤ) [IsPolyQ M] (hN : PolyT N) : IsPolyQ (QueryMachine.sumRange N M) :=
  foldRange M hN (by unfold Stepped.addG; fun_prop) (by unfold Stepped.zeroC; fun_prop)
@[instance_reducible] def prodRange [HasSize α] [Carried α] {N : α → ℕ} (M : QueryMachine Q A (α × ℕ) ℤ) [IsPolyQ M] (hN : PolyT N) : IsPolyQ (QueryMachine.prodRange N M) :=
  foldRange M hN (by unfold Stepped.mulG; fun_prop) (by unfold Stepped.oneC; fun_prop)
@[instance_reducible] def gated [HasSize α] [Carried α] (M : QueryMachine Q A α Bool) (N : QueryMachine Q A α ℤ) [IsPolyQ M] [IsPolyQ N] : IsPolyQ (QueryMachine.gated M N) :=
  haveI := mapIn (g := (Prod.fst : α × Bool → α)) (by fun_prop) N
  haveI : IsPolyQ (QueryMachine.const 0 : QueryMachine Q A (α × Bool) ℤ) := const 0
  haveI := ite (p := fun p : α × Bool => p.2) (by fun_prop) (QueryMachine.mapIn Prod.fst N) (QueryMachine.const 0)
  bind _ _
end derived
end IsPolyQ
section answer
variable [Enc Q] [Enc A] [Enc α] [Enc β]
@[instance_reducible] def ofOption_isPolyT [HasSize α] [HasSize β] [Carried α] [Carried β] {g : α → Option β} (hg : PolyT g) : IsPolyT (Stepped.ofOption g) where
  enc := (inferInstance : Enc (α ⊕ β))
  carried := (inferInstance : Carried (α ⊕ β))
  init := (by fun_prop : PolyT fun a : α => (.inl a : α ⊕ β))
  step := (by fun_prop : PolyT fun s : α ⊕ β => s.elim (fun a => (g a).elim (.inl a : α ⊕ β) fun b => .inr b) fun b => .inr b).congr fun s => by
    rcases s with a | b
    · change _ = (match g a with | some b => _ | none => _)
      simp only [Sum.elim_inl]
      cases g a <;> rfl
    · rfl
  out := (IsPolyT.ofFun_out (α := α) (β := β)).congr fun s => by cases s <;> rfl
@[instance_reducible] def close_isPolyT (M : QueryMachine Q A α β) [IsPolyQ M] {O : Q → Option A} (hO : PolyT O) : IsPolyT (M.close O) where
  enc := (inferInstance : Enc M.σ)
  carried := (inferInstance : Carried M.σ)
  init := IsPolyQ.init (M := M)
  step := by
    have h1 := IsPolyQ.ask (M := M); have h2 := IsPolyQ.step (M := M)
    have h3 : PolyT fun q : (M.σ × Q) × A => M.resume q.1.1 q.2 := PolyT.comp (g := fun q : (M.σ × Q) × A => (q.1.1, q.2)) (IsPolyQ.resume (M := M)) (by fun_prop)
    have h4 : PolyT fun q : M.σ × Q => (O q.2).elim q.1 fun v => M.resume q.1 v := PolyT.optionElim (by fun_prop) (by fun_prop) h3
    refine (PolyT.optionElim (o := fun s : M.σ => M.ask s) (d := fun s => M.step s) (f := fun s x => (O x).elim s fun v => M.resume s v) h1 h2 h4).congr fun s => ?_
    change _ = (match M.ask s with | some x => (match O x with | some v => M.resume s v | none => s) | none => M.step s)
    cases M.ask s with
    | none => rfl
    | some x => change _ = (match O x with | some v => M.resume s v | none => s); simp only [Option.elim_some]; cases O x <;> rfl
  out := IsPolyQ.out (M := M)
variable [HasSize C] [Enc C] [Carried C]
omit [Carried C] in
/-- The step of `plug` is polynomial-time. -/
theorem plug_step_poly (M : QueryMachine Q A α β) [IsPolyQ M] (R : Stepped (C × Q) A) [IsPolyT R] :
    @PolyT (C × (M.σ ⊕ (M.σ × R.σ))) (C × (M.σ ⊕ (M.σ × R.σ))) inferInstance inferInstance (M.plug R).step := by
  have h1 := IsPolyQ.ask (M := M); have h2 := IsPolyQ.step (M := M); have h3 := IsPolyT.init (M := R); have h4 := IsPolyT.step (M := R); have h5 := IsPolyT.out (M := R)
  have h6 : PolyT fun r : ((C × (M.σ ⊕ (M.σ × R.σ))) × (M.σ × R.σ)) × A => M.resume r.1.2.1 r.2 :=
    PolyT.comp (g := fun r : ((C × (M.σ ⊕ (M.σ × R.σ))) × (M.σ × R.σ)) × A => (r.1.2.1, r.2)) (IsPolyQ.resume (M := M)) (by fun_prop)
  have hG1 : PolyT fun q : (C × (M.σ ⊕ (M.σ × R.σ))) × M.σ => (M.ask q.2).elim ((q.1.1, .inl (M.step q.2)) : C × (M.σ ⊕ (M.σ × R.σ))) fun x => (q.1.1, .inr (q.2, R.init (q.1.1, x))) := by fun_prop
  have hG2 : PolyT fun q : (C × (M.σ ⊕ (M.σ × R.σ))) × (M.σ × R.σ) => (R.out q.2.2).elim ((q.1.1, .inr (q.2.1, R.step q.2.2)) : C × (M.σ ⊕ (M.σ × R.σ))) fun v => (q.1.1, .inl (M.resume q.2.1 v)) :=
    PolyT.optionElim (by fun_prop) (by fun_prop) (by fun_prop)
  refine (PolyT.sumElim (s := fun s : C × (M.σ ⊕ (M.σ × R.σ)) => s.2) (f := fun s m => (M.ask m).elim ((s.1, .inl (M.step m)) : C × (M.σ ⊕ (M.σ × R.σ))) fun x => (s.1, .inr (m, R.init (s.1, x))))
    (g := fun s p => (R.out p.2).elim ((s.1, .inr (p.1, R.step p.2)) : C × (M.σ ⊕ (M.σ × R.σ))) fun v => (s.1, .inl (M.resume p.1 v))) (by fun_prop) hG1 hG2).congr fun s => ?_
  rcases s with ⟨c, m | p⟩
  · change _ = (match M.ask m with | some x => _ | none => _)
    simp only [Sum.elim_inl]
    cases M.ask m <;> rfl
  · change _ = (match R.out p.2 with | some v => _ | none => _)
    simp only [Sum.elim_inr]
    cases R.out p.2 <;> rfl
@[instance_reducible] def plug_isPolyT (M : QueryMachine Q A α β) [IsPolyQ M] (R : Stepped (C × Q) A) [IsPolyT R] : IsPolyT (M.plug R) where
  enc := (inferInstance : Enc (C × (M.σ ⊕ (M.σ × R.σ))))
  carried := (inferInstance : Carried (C × (M.σ ⊕ (M.σ × R.σ))))
  init := by
    have h1 := IsPolyQ.init (M := M)
    exact (by fun_prop : PolyT fun x : C × α => ((x.1, .inl (M.init x.2)) : C × (M.σ ⊕ (M.σ × R.σ))))
  step := plug_step_poly M R
  out := by
    have h1 := IsPolyQ.out (M := M)
    exact (by fun_prop : PolyT fun s : C × (M.σ ⊕ (M.σ × R.σ)) => s.2.elim (fun m => M.out m) fun _ => none).congr fun s => by rcases s with ⟨c, m | p⟩ <;> rfl
variable [Enc Q'] [Enc A']
@[instance_reducible] def subst_isPolyQ (M : QueryMachine Q A α β) [IsPolyQ M] (N : QueryMachine Q' A' (C × Q) A) [IsPolyQ N] : IsPolyQ (M.subst N) where
  enc := (inferInstance : Enc (C × (M.σ ⊕ (M.σ × N.σ))))
  carried := (inferInstance : Carried (C × (M.σ ⊕ (M.σ × N.σ))))
  init := (plug_isPolyT M N.toStepped).init
  step := (plug_isPolyT M N.toStepped).step
  out := (plug_isPolyT M N.toStepped).out
  ask := by
    have h1 := IsPolyQ.out (M := N); have h2 := IsPolyQ.ask (M := N)
    refine (by fun_prop : PolyT fun s : C × (M.σ ⊕ (M.σ × N.σ)) => s.2.elim (fun _ => none) fun p => (N.out p.2).elim (N.ask p.2) fun _ => none).congr fun s => ?_
    rcases s with ⟨c, m | p⟩
    · rfl
    · change _ = (match N.out p.2 with | some _ => none | none => N.ask p.2)
      simp only [Sum.elim_inr]
      cases N.out p.2 <;> rfl
  resume := by
    have h1 : PolyT fun q : ((C × (M.σ ⊕ (M.σ × N.σ))) × A') × (M.σ × N.σ) => N.resume q.2.2 q.1.2 :=
      PolyT.comp (g := fun q : ((C × (M.σ ⊕ (M.σ × N.σ))) × A') × (M.σ × N.σ) => (q.2.2, q.1.2)) (IsPolyQ.resume (M := N)) (by fun_prop)
    refine (PolyT.sumElim (s := fun q : (C × (M.σ ⊕ (M.σ × N.σ))) × A' => q.1.2) (f := fun q _ => q.1)
      (g := fun q p => ((q.1.1, .inr (p.1, N.resume p.2 q.2)) : C × (M.σ ⊕ (M.σ × N.σ)))) (by fun_prop) (by fun_prop) (by fun_prop)).congr fun q => ?_
    rcases q with ⟨⟨c, m | p⟩, v⟩ <;> rfl
end answer
end QueryMachines.QueryMachine
namespace QueryMachines
open Groundwork QueryMachine
end QueryMachines


