-- Prove2me | Definitions.Def_CountedToPadded_Compare
-- name    : CountedToPadded_Compare
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:22:28.21549+00:00
-- url     : https://prove2.me/theorems/879efcbd-68c3-4367-bdb2-c63ed894de42
-- title:
--   Compare
-- statement:
--   Definitions and structural lemmas for Compare, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Compare.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Bool
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_idxOf
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_nilHead_cons
import Theorems.Thm_Groundwork_PolyT_nilHead_nil
import Theorems.Thm_Groundwork_PolyT_of
import Theorems.Thm_Groundwork_PolyT_optionElim
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_PolyT_sumElim
import Theorems.Thm_Groundwork_PolyT_tagF_within
import Theorems.Thm_Groundwork_PolyT_testBit
import Theorems.Thm_Groundwork_PolyT_within_branch
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_seq
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
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
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
@[expose] section
namespace QueryMachines.Bridge.Proof
open Turing Groundwork Groundwork.TM Groundwork.PolyT
scoped instance encV : Enc V := ⟨id⟩
def vSplit : V → Unit ⊕ (Bool ⊕ V × V)
  | .nil => .inl ()
  | .bit b => .inr (.inl b)
  | .cons x y => .inr (.inr (x, y))
def bitHead : TM2.Stmt (fun _ : Stk => Sym) Bool (Option Sym) :=
  .peek .main (fun _ o => o) <|
    .branch (fun s => s == some .L) (.load (fun _ => none) <| .goto fun _ => false) (.load (fun _ => none) <| .goto fun _ => true)
theorem bitHead_bit (b : Bool) (M A B N : List Sym) : TM2.stepAux bitHead none (st (.bit b :: M) A B N) = ⟨some true, none, st (.bit b :: M) A B N⟩ := by
  simp [bitHead, TM2.stepAux]
theorem bitHead_L (M A B N : List Sym) : TM2.stepAux bitHead none (st (.L :: M) A B N) = ⟨some false, none, st (.L :: M) A B N⟩ := by
  simp [bitHead, TM2.stepAux]
theorem length_code_tag (b : Bool) (x : V) : (code (.cons (.bit b) x)).length = (code x).length + 3 := by
  simp [code]
theorem vSplit_poly : PolyT vSplit := by
  refine PolyT.of (Frag.branch bitHead ((tagF false).seq (tagF true)) (Frag.branch nilHead ((tagF true).seq (tagF true)) (tagF false)))
    (t := fun n => 4 * n + 30) (s := fun n => n + 6) (((PB.const 4).mul PB.id').add (PB.const 30)) (PB.id'.add (PB.const 6)) (fun v M A B N => ?_) (fun v => ?_)
  · have hl : len v = (code v).length := rfl
    cases v with
    | nil =>
      have c := tagF_within false .nil M A B N
      have h1 := within_branch (P := (tagF true).seq (tagF true)) (Q := tagF false) false (nilHead_nil M A B N) c
      have h2 := within_branch (P := (tagF false).seq (tagF true)) (Q := Frag.branch nilHead ((tagF true).seq (tagF true)) (tagF false)) false (bitHead_L (.R :: M) A B N) h1
      exact h2.mono (by rw [hl]; omega)
    | bit b =>
      have c1 := tagF_within false (.bit b) M A B N
      have c2 := tagF_within true (.cons (.bit false) (.bit b)) M A B N
      have h2 := within_branch (P := (tagF false).seq (tagF true)) (Q := Frag.branch nilHead ((tagF true).seq (tagF true)) (tagF false)) true (bitHead_bit b M A B N) (c1.seq c2)
      exact h2.mono (by rw [hl, length_code_tag]; omega)
    | cons x y =>
      have e0 : code (.cons x y) ++ M = .L :: (code x ++ (code y ++ [.R] ++ M)) := by simp [code]
      have hn := nilHead_cons x (code y ++ [.R] ++ M) A B N
      have hb := bitHead_L (code x ++ (code y ++ [.R] ++ M)) A B N
      rw [← e0] at hn hb
      have c1 := tagF_within true (.cons x y) M A B N
      have c2 := tagF_within true (.cons (.bit true) (.cons x y)) M A B N
      have h1 := within_branch (P := (tagF true).seq (tagF true)) (Q := tagF false) true hn (c1.seq c2)
      have h2 := within_branch (P := (tagF false).seq (tagF true)) (Q := Frag.branch nilHead ((tagF true).seq (tagF true)) (tagF false)) false hb h1
      exact h2.mono (by rw [hl, length_code_tag]; omega)
  · cases v with
    | nil => exact (by decide : (5 : ℕ) ≤ 2 + 6)
    | bit b => exact (by decide : (7 : ℕ) ≤ 1 + 6)
    | cons x y =>
      show (code (.cons (.bit true) (.cons (.bit true) (.cons x y)))).length ≤ (code (.cons x y)).length + 6
      rw [length_code_tag, length_code_tag]
@[local fun_prop] theorem vSplit' {α : Type} [Enc α] {f : α → V} (hf : PolyT f) : PolyT fun x => vSplit (f x) := comp vSplit_poly hf
def visit (s : List V × ℕ) : List V × ℕ :=
  s.1.head?.elim s fun v => (vSplit v).elim (fun _ => (s.1.tail, s.2 + 2)) fun t => t.elim (fun _ => (s.1.tail, s.2 + 1)) fun p => (p.1 :: p.2 :: s.1.tail, s.2 + 2)
def total (w : List V) : ℕ := (w.map fun v => (code v).length).sum
def nodes : V → ℕ
  | .nil => 1
  | .bit _ => 1
  | .cons x y => nodes x + nodes y + 1
def work (w : List V) : ℕ := (w.map nodes).sum
def cmp (p : List Unit × V) : Bool := (p.1.foldl (fun s _ => visit s) ([p.2], 0)).1.isEmpty && decide ((p.1.foldl (fun s _ => visit s) ([p.2], 0)).2 ≤ p.1.length)
end QueryMachines.Bridge.Proof


