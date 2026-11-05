-- Prove2me | Definitions.Def_Occ_Main
-- name    : Occ_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:43:54.867272+00:00
-- url     : https://prove2.me/theorems/2ac1c707-5251-4b20-8d22-e19932471c18
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Occ/Main.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Occ_Defs
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_CountKSat_InOut
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Int
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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


set_option autoImplicit false
section
section
@[expose] section
namespace Occ
open Groundwork Groundwork.Prog CountKSat
theorem mem_occurring {Φ : Fml} {v : ℕ} : v ∈ Eight.occurring Φ ↔ ∃ C ∈ Φ, ∃ l ∈ C, l.1 = v := by
  simp only [Eight.occurring, List.mem_toFinset, List.mem_map, List.mem_flatten]
  constructor
  · rintro ⟨l, ⟨C, hC, hl⟩, rfl⟩
    exact ⟨C, hC, l, hl, rfl⟩
  · rintro ⟨C, hC, l, hl, rfl⟩
    exact ⟨l, ⟨C, hC, hl⟩, rfl⟩
theorem lt_of_mem_occurring {n : ℕ} {Φ : Fml} (h : Below n Φ) {v : ℕ} (hv : v ∈ Eight.occurring Φ) : v < n := by
  obtain ⟨C, hC, l, hl, rfl⟩ := mem_occurring.1 hv
  exact h C hC l hl
theorem below_toN {N : ℕ} (φ : Sat3.CNF N) : Below N (Decode.toN φ) := by
  intro C' hC' l' hl'
  obtain ⟨C, -, rfl⟩ := List.mem_map.1 hC'
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hl'
  exact l.1.2
theorem val_mem_occurring {N : ℕ} (φ : Sat3.CNF N) (i : Fin N) : i.val ∈ Eight.occurring (Decode.toN φ) ↔ MainTheoremForms.Occurs φ i := by
  rw [mem_occurring]
  constructor
  · rintro ⟨C', hC', l', hl', h⟩
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hC'
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hl'
    exact ⟨C, hC, l, hl, Fin.ext h⟩
  · rintro ⟨C, hC, l, hl, rfl⟩
    exact ⟨_, List.mem_map_of_mem hC, _, List.mem_map_of_mem hl, rfl⟩
def occEquiv {N : ℕ} (φ : Sat3.CNF N) : {v : ℕ // v ∈ Eight.occurring (Decode.toN φ)} ≃ {i : Fin N // MainTheoremForms.Occurs φ i} where
  toFun v := ⟨⟨v.1, lt_of_mem_occurring (below_toN φ) v.2⟩, (val_mem_occurring φ _).1 v.2⟩
  invFun i := ⟨i.1.val, (val_mem_occurring φ i.1).2 i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
end Occ


