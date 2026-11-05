-- Prove2me | Definitions.Def_VariableBound_Paper_Rename_Math
-- name    : VariableBound_Paper_Rename_Math
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:33:13.793795+00:00
-- url     : https://prove2.me/theorems/a0ad59ac-6a2f-4899-ac45-e60deb28ae74
-- title:
--   Math
-- statement:
--   Definitions and structural lemmas for Math, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Math.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_VariableBound_Paper_Rename_Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Dedup
import Mathlib.Logic.Equiv.Prod
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_idxOf
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
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
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.idxOf
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
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
namespace VariableBound.Rename
open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Sat3 (CNF)
theorem mem_occL {ψ : Fml} {v : ℕ} : v ∈ occL ψ ↔ ∃ C ∈ ψ, ∃ l ∈ C, l.1 = v := by
  simp only [occL, List.mem_dedup, List.mem_flatMap, List.mem_map]
theorem nodup_occL (ψ : Fml) : (occL ψ).Nodup := List.nodup_dedup _
variable {N : ℕ} (φ : CNF N)
theorem val_mem_occL {i : Fin N} : i.val ∈ occL (toN φ) ↔ Occurs φ i := by
  rw [mem_occL]
  constructor
  · rintro ⟨C, hC, l, hl, h⟩
    obtain ⟨C', hC', rfl⟩ := List.mem_map.1 hC
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    exact ⟨C', hC', l', hl', Fin.ext h⟩
  · rintro ⟨C, hC, l, hl, h⟩
    exact ⟨_, List.mem_map_of_mem hC, _, List.mem_map_of_mem hl, congrArg Fin.val h⟩
theorem exists_of_mem_occL {v : ℕ} (h : v ∈ occL (toN φ)) : ∃ i : Fin N, i.val = v ∧ Occurs φ i := by
  obtain ⟨C, hC, l, hl, rfl⟩ := mem_occL.1 h
  obtain ⟨C', hC', rfl⟩ := List.mem_map.1 hC
  obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
  exact ⟨l'.1, rfl, C', hC', l', hl', rfl⟩
def pos0 (i : {i : Fin N // Occurs φ i}) : Fin (occL (toN φ)).length :=
  ⟨(occL (toN φ)).idxOf i.1.val, List.idxOf_lt_length_iff.2 ((val_mem_occL φ).2 i.2)⟩
theorem pos0_bijective : Function.Bijective (pos0 φ) := by
  constructor
  · intro i j h
    have h' : (occL (toN φ)).idxOf i.1.val = (occL (toN φ)).idxOf j.1.val := congrArg Fin.val h
    exact Subtype.ext (Fin.ext ((List.idxOf_inj ((val_mem_occL φ).2 i.2)).1 h'))
  · intro j
    obtain ⟨i, hi, ho⟩ := exists_of_mem_occL φ (List.getElem_mem j.2)
    refine ⟨⟨i, ho⟩, Fin.ext ?_⟩
    simp only [pos0, hi]
    exact (nodup_occL _).idxOf_getElem j.1 j.2
theorem length_occL : (occL (toN φ)).length = numOcc φ := by
  rw [numOcc, Nat.card_congr (Equiv.ofBijective _ (pos0_bijective φ)), Nat.card_eq_fintype_card, Fintype.card_fin]
noncomputable def pos : {i : Fin N // Occurs φ i} ≃ Fin (numOcc φ) :=
  (Equiv.ofBijective _ (pos0_bijective φ)).trans (finCongr (length_occL φ))
open Classical in
/-- φ with the variables that occur renamed to 0, …, n − 1. -/
noncomputable def ren : CNF (numOcc φ) :=
  φ.map fun C => C.filterMap fun l => if h : Occurs φ l.1 then some (pos φ ⟨l.1, h⟩, l.2) else none
end VariableBound.Rename


