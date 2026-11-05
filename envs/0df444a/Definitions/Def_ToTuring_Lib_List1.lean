-- Prove2me | Definitions.Def_ToTuring_Lib_List1
-- name    : ToTuring_Lib_List1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:31:51.59601+00:00
-- url     : https://prove2.me/theorems/679673ea-038a-49a6-afdd-bf4eaa869733
-- title:
--   List1
-- statement:
--   Definitions and structural lemmas for List1, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List1.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Bool
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_foldl_add
import Theorems.Thm_Groundwork_PolyT_fst
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
import Theorems.Thm_Groundwork_len_le_of_mem
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
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_P2M_Groundwork_PolyT_inl__78f4b62d65a1
import Theorems.Thm_P2M_Groundwork_PolyT_inr__53ca1f30b2d3
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
import Theorems.Thm_P2M_Groundwork_PolyT_some__e6a32bd6af45
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.optionElim
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sumElim
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86
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
theorem len_bound {f : α → β} (hf : PolyT f) : ∃ t, PB t ∧ Monotone t ∧ ∀ x, len (f x) ≤ t (len x) := by
  obtain ⟨_, t, ht, hm, _, hlen⟩ := hf.elim
  exact ⟨t, ht, hm, hlen⟩
omit [Enc β] in
theorem foldl_cons_eq (l acc : List β) : l.foldl (fun c e => e :: c) acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons e l ih => simp [ih]
theorem reverseAppend {l l' : α → List β} (hl : PolyT l) (hl' : PolyT l') :
    PolyT (fun x => (l x).reverse ++ l' x) := by
  obtain ⟨s, hs, _, hls⟩ := len_bound hl
  have h : PolyT (fun x => (l x).foldl (fun c e => e :: c) (l' x)) := by
    refine foldl_add (g := fun _ c e => e :: c) hl hl' (by fun_prop) ⟨fun n => s n + 2, hs.add (PB.const 2), ?_⟩
    intro x c e he
    have := (len_le_of_mem he).trans (hls x)
    simp only [len_cons]
    omega
  exact h.congr fun x => foldl_cons_eq _ _
@[fun_prop] theorem reverse {l : α → List β} (hl : PolyT l) :
    PolyT (fun x => (l x).reverse) :=
  (reverseAppend hl (const [])).congr fun x => by simp
@[fun_prop] theorem append {l l' : α → List β} (hl : PolyT l) (hl' : PolyT l') :
    PolyT (fun x => l x ++ l' x) :=
  (reverseAppend (reverse hl) hl').congr fun x => by simp
theorem foldr {l : α → List ε} {a : α → γ} {g : α → ε → γ → γ} (hl : PolyT l) (ha : PolyT a)
    (hg : PolyT fun p : α × ε × γ => g p.1 p.2.1 p.2.2)
    (hB : ∃ t, PB t ∧ ∀ x (k : ℕ), len (((l x).drop k).foldr (g x) (a x)) ≤ t (len x)) :
    PolyT (fun x => (l x).foldr (g x) (a x)) := by
  obtain ⟨t, ht, hB⟩ := hB
  have hg' : PolyT fun p : α × γ × ε => g p.1 p.2.2 p.2.1 :=
    PolyT.comp (f := fun p : α × ε × γ => g p.1 p.2.1 p.2.2) (g := fun p : α × γ × ε => (p.1, p.2.2, p.2.1)) hg
      (by fun_prop)
  have h : PolyT (fun x => (l x).reverse.foldl (fun c e => g x e c) (a x)) := by
    refine foldl (g := fun x c e => g x e c) (reverse hl) ha hg' ⟨t, ht, fun x k => ?_⟩
    rw [List.take_reverse, List.foldl_reverse]
    exact hB x _
  exact h.congr fun x => by rw [List.foldl_reverse]
end Groundwork.PolyT


