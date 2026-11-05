-- Prove2me | Definitions.Def_VariableBound_Field_Quot
-- name    : VariableBound_Field_Quot
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:48:07.749613+00:00
-- url     : https://prove2.me/theorems/fc6a44c1-d0d6-44a1-905d-37cb9bca478d
-- title:
--   Quot
-- statement:
--   Definitions and structural lemmas for Quot, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Alg
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
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
@[expose] section
namespace VariableBound.Fld
open Polynomial
namespace Quot
theorem map_bitR {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (b : Bool) : φ (bitR R b) = bitR S b := by
  cases b <;> simp [bitR]
theorem coeff_polyW (w : List Bool) (i : ℕ) : (polyW w).coeff i = bitR (ZMod 2) (w.getD i false) := by
  induction w generalizing i with
  | nil => simp [polyW, decR, bitR]
  | cons b w ih =>
    have h : polyW (b :: w) = C (bitR (ZMod 2) b) + X * polyW w := by
      rw [polyW, decR, ← map_bitR (C : ZMod 2 →+* (ZMod 2)[X])]
      rfl
    rw [h, coeff_add]
    cases i with
    | zero => simp
    | succ i => simp [coeff_X_mul, ih, coeff_C_succ]
end Quot
open VariableBound.Fld.Quot
theorem degree_polyW_lt (w : List Bool) : (polyW w).degree < w.length := by
  rw [degree_lt_iff_coeff_zero]
  intro i hi
  rw [coeff_polyW, List.getD_eq_default _ _ hi]
  rfl
theorem monic_modP (g : List Bool) : (modP g).Monic :=
  monic_X_pow_add (degree_polyW_lt g)
theorem natDegree_modP (g : List Bool) : (modP g).natDegree = g.length := by
  rw [modP, add_comm]
  exact natDegree_add_eq_right_of_degree_lt (by rw [degree_X_pow]; exact degree_polyW_lt g) |>.trans (natDegree_X_pow _)
@[expose] noncomputable def bitsW (g : List Bool) : FW g ≃ₗ[ZMod 2] (Fin g.length → ZMod 2) :=
  (AdjoinRoot.powerBasisAux' (monic_modP g)).equivFun.trans (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finCongr (natDegree_modP g).symm))
end VariableBound.Fld


