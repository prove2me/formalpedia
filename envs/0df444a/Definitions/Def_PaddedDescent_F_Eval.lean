-- Prove2me | Definitions.Def_PaddedDescent_F_Eval
-- name    : PaddedDescent_F_Eval
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:31:07.635468+00:00
-- url     : https://prove2.me/theorems/ee9210bb-0964-489a-a0ca-9ef37ded7d66
-- title:
--   Eval
-- statement:
--   Definitions and structural lemmas for Eval, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Eval.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_ToTuring_EncLemmas
import Theorems.Thm_Groundwork_PolyT_length
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
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea
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
namespace PaddedDescent.F.Eval
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open PaddedDescent.F.Mark (Cl trunc Good nSat occ placeAt placeE layersE Asked MCtx markF markN adm nProf cls WfL)
theorem take_getD_drop {Ls : List Fml} {i : ℕ} (h : i < Ls.length) : Ls.take i ++ Ls.getD i [] :: Ls.drop (i + 1) = Ls := by
  rw [List.getD_eq_getElem _ _ h, ← List.drop_eq_getElem_cons h, List.take_append_drop]
structure Form (k n R c : ℕ) (Ls : List Fml) : Prop where
  layers : Ls.length = R + 1
  wf : WfL k n Ls
  card : Ls.flatten.length = c
theorem Form.placeAt {k n R c : ℕ} {Ls : List Fml} (h : Form k n R c Ls) {C : Cl} (hC : C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) {i : ℕ}
    (hi : i < Ls.length) : Form k n R (c + 1) (placeAt Ls C i) := by
  have e := take_getD_drop hi
  refine ⟨?_, ?_, ?_⟩
  · rw [← h.layers]
    conv_rhs => rw [← e]
    simp [Mark.placeAt]
  · intro L hL D hD
    have hmem : ∀ L' ∈ Ls.take i ++ Ls.getD i [] :: Ls.drop (i + 1), ∀ D ∈ L', D ≠ [] ∧ D.length ≤ k ∧ ∀ l ∈ D, l.1 < n := by
      rw [e]; exact h.wf
    simp only [Mark.placeAt, List.mem_append, List.mem_cons] at hL
    rcases hL with hL | rfl | hL
    · exact hmem L (by simp [hL]) D hD
    · rcases List.mem_cons.1 hD with rfl | hD
      · exact hC
      · exact hmem _ (by simp) D hD
    · exact hmem L (by simp [hL]) D hD
  · rw [← h.card]
    conv_rhs => rw [← e]
    simp [Mark.placeAt]
    omega
theorem Form.placeE {k n R c : ℕ} {Ls : List Fml} (h : Form k n R c Ls) (ev : List Fml → ℤ) (w : ℕ) {C : Cl}
    (hC : C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) : Form k n R (c + 1) (placeE ev w Ls C) := by
  refine h.placeAt hC ?_
  have hl := h.layers
  cases hf : (List.range (Ls.length - 1)).find? (Mark.dropE ev w Ls C) with
  | none => simp only [Option.getD_none]; omega
  | some i =>
    have := List.mem_range.1 (List.mem_of_find?_eq_some hf)
    simp only [Option.getD_some]
    omega
end PaddedDescent.F.Eval


